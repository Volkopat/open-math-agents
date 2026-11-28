import OMAStatements.S_oeis_a064377
import Mathlib

namespace OMA.DivisorFourthTrial

private def candidates : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

private theorem candidates_sound : ∀ p ∈ candidates, p.Prime := by decide +kernel

private theorem candidates_complete : ∀ p : Fin 72, p.val.Prime → p.val ∈ candidates := by decide +kernel

private def firstPrime (n : ℕ) : ℕ :=
  (candidates.find? (fun p => n % p == 0)).getD n

private theorem firstPrime_sound (n : ℕ) (lower : 2 ≤ n) (upper : n < 5163) :
    (firstPrime n).Prime ∧ firstPrime n ∣ n := by
  unfold firstPrime
  cases h : candidates.find? (fun p => n % p == 0) with
  | none =>
    simp only [Option.getD_none]
    refine ⟨?_,dvd_refl _⟩
    by_contra composite
    let p := n.minFac
    have prime : p.Prime := Nat.minFac_prime (by omega)
    have square : p^2 ≤ n := Nat.minFac_sq_le_self (by omega) composite
    have small : p < 72 := by
      by_contra! tooLarge
      have large : (72:ℕ)^2 ≤ p^2 := Nat.pow_le_pow_left tooLarge 2
      omega
    have found : p ∈ candidates := candidates_complete ⟨p,small⟩ prime
    have divides : p ∣ n := Nat.minFac_dvd n
    exact List.find?_eq_none.mp h p found (by simpa [Nat.mod_eq_zero_of_dvd divides])
  | some p =>
    simp only [Option.getD_some]
    have found := List.mem_of_find?_eq_some h
    have zero : n % p = 0 := by simpa using List.find?_some h
    exact ⟨candidates_sound p found, Nat.dvd_of_mod_eq_zero zero⟩

private def factors : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel+1, n =>
      if n < 2 then [] else
      let p := firstPrime n
      p :: factors fuel (n/p)

private theorem factors_sound (fuel n : ℕ) (positive : 0 < n)
    (upper : n < 5163) (enough : n < 2^fuel) :
    (factors fuel n).prod = n ∧ ∀ p ∈ factors fuel n, p.Prime := by
  induction fuel generalizing n with
  | zero => simp at enough; omega
  | succ fuel ih =>
    by_cases small : n < 2
    · have one : n = 1 := by omega
      subst n
      simp [factors]
    · let p := firstPrime n
      have ⟨prime, div⟩ := firstPrime_sound n (by omega) upper
      have ppositive : 0 < p := prime.pos
      have lower : p ≤ n := Nat.le_of_dvd positive div
      have posQuot : 0 < n/p := Nat.div_pos lower ppositive
      have upperQuot : n/p < 5163 := (Nat.div_le_self _ _).trans_lt upper
      have power : n/p < 2^fuel := by
        apply (Nat.div_lt_iff_lt_mul ppositive).mpr
        rw [pow_succ] at enough
        exact enough.trans_le (Nat.mul_le_mul_left _ prime.two_le)
      have ⟨product, primes⟩ := ih (n/p) posQuot upperQuot power
      rw [factors, if_neg small]
      change (p :: factors fuel (n/p)).prod = n ∧
        ∀ q ∈ p :: factors fuel (n/p), q.Prime
      refine ⟨?_,?_⟩
      · rw [List.prod_cons,product,Nat.mul_comm p, Nat.div_mul_cancel div]
      · intro q mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact prime
        · exact primes q mem

private theorem factors_perm (n : ℕ) (positive : 0 < n) (upper : n < 5163) :
    (factors 13 n).Perm n.primeFactorsList := by
  have ⟨prod,primes⟩ := factors_sound 13 n positive upper (by omega)
  exact Nat.primeFactorsList_unique prod primes

def phi (n : ℕ) : ℕ :=
  let ps := (factors 13 n).toFinset
  (n * ∏ p ∈ ps, (p-1)) / (∏ p ∈ ps, p)

def sigmaFour (n : ℕ) : ℕ :=
  let fs := factors 13 n
  ∏ p ∈ fs.toFinset, ∑ k ∈ Finset.range (fs.count p+1), p^(4*k)

theorem phi_eq (n : ℕ) (positive : 0 < n) (upper : n < 5163) : phi n = n.totient := by
  have support := List.toFinset_eq_of_perm _ _ (factors_perm n positive upper)
  unfold phi
  rw [support]
  change (n * ∏ p ∈ n.primeFactors, (p-1)) / (∏ p ∈ n.primeFactors, p) = n.totient
  have nonzero : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  rw [← Nat.totient_mul_prod_primeFactors n, Nat.mul_div_cancel _ nonzero]

theorem sigmaFour_eq (n : ℕ) (positive : 0 < n) (upper : n < 5163) :
    sigmaFour n = ∑ d ∈ n.divisors, d^4 := by
  have perm := factors_perm n positive upper
  have support := List.toFinset_eq_of_perm _ _ perm
  rw [← ArithmeticFunction.sigma_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (by omega : n ≠ 0)]
  dsimp only [sigmaFour]
  rw [support]
  simp only [perm.count_eq, Nat.primeFactorsList_count_eq, Nat.mul_comm 4]
  rfl

end OMA.DivisorFourthTrial

namespace OMA.DivisorFourthRange

private def small : Finset ℕ := {2,3,5,7}

private theorem prime_large (p : ℕ) (prime : p.Prime) (outside : p ∉ small) :
    11 ≤ p := by
  by_contra! bound
  have check : ∀ p : Fin 11, p.val.Prime → p.val ∈ small := by decide +kernel
  exact outside (check ⟨p,bound⟩ prime)

private def admissible (bound numerator denominator : ℕ) : Prop :=
  ∀ k : Fin 5, ∀ u ∈ small.powerset,
    (∏ p ∈ u, p) * 11^k.val < bound →
    numerator * (∏ p ∈ u, p) * 11^k.val ≤ denominator * (∏ p ∈ u, (p-1)) * 10^k.val

private theorem ratio_of_admissible (n bound a b : ℕ) (positive : 0 < n)
    (below : n < bound) (bound_le : bound ≤ 81920)
    (checked : admissible bound a b) : a*n ≤ b*n.totient := by
  let s := n.primeFactors
  let u := s ∩ small
  let v := s \ u
  let k := v.card
  have included : u ⊆ s := Finset.inter_subset_left
  have large (p : ℕ) (member : p ∈ v) : 11 ≤ p := by
    have hm := Finset.mem_sdiff.mp member
    exact prime_large p (Nat.prime_of_mem_primeFactors hm.1)
      (fun smallMember => hm.2 (Finset.mem_inter.mpr ⟨hm.1,smallMember⟩))
  have split (f : ℕ → ℕ) : (∏ p ∈ u, f p)*(∏ p ∈ v, f p) = ∏ p ∈ s, f p := by
    rw [mul_comm]
    exact Finset.prod_sdiff included
  have product_le : (∏ p ∈ s, p) ≤ n := Nat.le_of_dvd positive (Nat.prod_primeFactors_dvd n)
  have big_le : 11^k ≤ ∏ p ∈ v, p := by
    calc
      11^k = (∏ _p ∈ v, (11:ℕ)) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ v, p := Finset.prod_le_prod' large
  have lower : (∏ p ∈ u, p)*11^k ≤ n := by
    rw [← split (fun p => p)] at product_le
    exact (Nat.mul_le_mul_left _ big_le).trans product_le
  have positiveSmall : 0 < ∏ p ∈ u, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (included hp)).pos)
  have short : k < 5 := by
    by_contra! long
    have pow : (11:ℕ)^5 ≤ 11^k := Nat.pow_le_pow_right (by decide) long
    have bounded : 11^k ≤ n := by
      calc
        11^k = 1*11^k := by simp
        _ ≤ (∏ p ∈ u, p)*11^k := Nat.mul_le_mul_right _ (by omega)
        _ ≤ n := lower
    omega
  have pair := checked ⟨k,short⟩ u
    (Finset.mem_powerset.mpr Finset.inter_subset_right) (lower.trans_lt below)
  have largeRatio : 10^k*(∏ p ∈ v, p) ≤ 11^k*(∏ p ∈ v, (p-1)) := by
    calc
      10^k*(∏ p ∈ v, p) = ∏ p ∈ v, 10*p := by
        rw [Finset.prod_mul_distrib,Finset.prod_const]
      _ ≤ ∏ p ∈ v, 11*(p-1) := Finset.prod_le_prod' (fun p hp => by have := large p hp; omega)
      _ = 11^k*(∏ p ∈ v, (p-1)) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const]
  have products : a*(∏ p ∈ s, p) ≤ b*(∏ p ∈ s, (p-1)) := by
    refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < 11^k)
    rw [← split (fun p => p), ← split (fun p => p-1)]
    calc
      11^k*(a*((∏ p ∈ u, p)*(∏ p ∈ v, p))) =
          (a*(∏ p ∈ u, p)*11^k)*(∏ p ∈ v, p) := by ring
      _ ≤ (b*(∏ p ∈ u, (p-1))*10^k)*(∏ p ∈ v, p) := Nat.mul_le_mul_right _ pair
      _ = (b*(∏ p ∈ u, (p-1)))*(10^k*(∏ p ∈ v, p)) := by ring
      _ ≤ (b*(∏ p ∈ u, (p-1)))*(11^k*(∏ p ∈ v, (p-1))) := Nat.mul_le_mul_left _ largeRatio
      _ = 11^k*(b*((∏ p ∈ u, (p-1))*(∏ p ∈ v, (p-1)))) := by ring
  have euler : n.totient*(∏ p ∈ s, p) = n*(∏ p ∈ s, (p-1)) :=
    Nat.totient_mul_prod_primeFactors n
  have scale : 0 < ∏ p ∈ s, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  apply Nat.le_of_mul_le_mul_right ?_ scale
  calc
    (a*n)*(∏ p ∈ s, p) = n*(a*(∏ p ∈ s, p)) := by ring
    _ ≤ n*(b*(∏ p ∈ s, (p-1))) := Nat.mul_le_mul_left _ products
    _ = (b*n.totient)*(∏ p ∈ s, p) := by
      rw [show n*(b*(∏ p ∈ s, (p-1))) = b*(n*(∏ p ∈ s, (p-1))) by ring,← euler]
      ring

private theorem power_bound (n a b : ℕ) (bpos : 0 < b) (ratio : a*n ≤ b*n.totient)
    (large : 2*b^5 ≤ a^5*n) : 2*n^4 ≤ n.totient^5 := by
  have raised := Nat.pow_le_pow_left ratio 5
  simp only [mul_pow] at raised
  apply Nat.le_of_mul_le_mul_right ?_ (pow_pos bpos 5)
  calc
    (2*n^4)*b^5 = (2*b^5)*n^4 := by ring
    _ ≤ (a^5*n)*n^4 := Nat.mul_le_mul_right _ large
    _ = a^5*n^5 := by ring
    _ ≤ b^5*n.totient^5 := raised
    _ = n.totient^5*b^5 := by ring

theorem upper_exclusion (n : ℕ) (lower : 5163 ≤ n) (upper : n < 81920) :
    2*n^4 ≤ n.totient^5 := by
  by_cases near : n < 8315
  · have checked : admissible 8315 16 77 := by unfold admissible; decide +kernel
    have ratio := ratio_of_admissible n 8315 16 77 (by omega) near (by decide) checked
    apply power_bound n 16 77 (by decide) ratio
    norm_num
    omega
  · have checked : admissible 81920 160 847 := by unfold admissible; decide +kernel
    have ratio := ratio_of_admissible n 81920 160 847 (by omega) upper (by decide) checked
    apply power_bound n 160 847 (by decide) ratio
    norm_num
    omega

end OMA.DivisorFourthRange

namespace OMA.DivisorFourthPowers

private theorem reciprocal_step (x : ℚ) (hx : 0 < x) :
    1 / (x+1)^4 ≤ 1/x - 1/(x+1) := by
  have hy : 0 < x+1 := by linarith
  have one : 1 ≤ x+1 := by linarith
  have denominator : x*(x+1) ≤ (x+1)^4 := by
    calc
      x*(x+1) ≤ (x+1)*(x+1) := by gcongr; linarith
      _ = (x+1)^2 := by ring
      _ ≤ (x+1)^4 := pow_le_pow_right₀ one (by decide)
  calc
    1 / (x+1)^4 ≤ 1 / (x*(x+1)) :=
      one_div_le_one_div_of_le (mul_pos hx hy) denominator
    _ = 1/x - 1/(x+1) := by
      field_simp [ne_of_gt hx, ne_of_gt hy] <;> ring

private theorem reciprocal_range (m : ℕ) :
    (∑ i ∈ Finset.range (m+1), (1:ℚ)/((i:ℚ)+1)^4) ≤ 2 - 1/((m:ℚ)+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have step := reciprocal_step ((m:ℚ)+1) (by positivity)
    push_cast
    linarith

private theorem reciprocal_divisors (n : ℕ) (positive : 0 < n) :
    (∑ d ∈ n.divisors, (1:ℚ)/(d:ℚ)^4) ≤ 2 := by
  let successor : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  have subset : n.divisors ⊆ (Finset.range n).map successor := by
    intro d hd
    have divides := Nat.dvd_of_mem_divisors hd
    have lo := Nat.pos_of_dvd_of_pos divides positive
    have hi := Nat.le_of_dvd positive divides
    refine Finset.mem_map.mpr ⟨d-1, Finset.mem_range.mpr (by omega), ?_⟩
    change d-1+1 = d
    omega
  have comparison : (∑ d ∈ n.divisors, (1:ℚ)/(d:ℚ)^4) ≤
      ∑ d ∈ (Finset.range n).map successor, (1:ℚ)/(d:ℚ)^4 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg subset
    intro d _ _
    positivity
  rw [Finset.sum_map] at comparison
  have range : (∑ i ∈ Finset.range n, (1:ℚ)/((i:ℚ)+1)^4) ≤ 2 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine (reciprocal_range m).trans ?_
    have positiveReciprocal : (0:ℚ) ≤ 1/((m:ℚ)+1) := by positivity
    linarith
  exact (by simpa [successor, Nat.cast_succ] using comparison :
    (∑ d ∈ n.divisors, (1:ℚ)/(d:ℚ)^4) ≤
      ∑ i ∈ Finset.range n, (1:ℚ)/((i:ℚ)+1)^4).trans range

theorem sigmaFour_le_two (n : ℕ) (positive : 0 < n) :
    (∑ d ∈ n.divisors, d^4) ≤ 2*n^4 := by
  have bound : (∑ d ∈ n.divisors, (d:ℚ)^4) ≤ 2*(n:ℚ)^4 := by
    calc
      (∑ d ∈ n.divisors, (d:ℚ)^4) =
          ∑ q ∈ n.divisors, ((n/q : ℕ):ℚ)^4 :=
        (Nat.sum_div_divisors n (fun q : ℕ => (q:ℚ)^4)).symm
      _ = (n:ℚ)^4 * ∑ q ∈ n.divisors, (1:ℚ)/(q:ℚ)^4 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have divides := Nat.dvd_of_mem_divisors hq
        have qpos := Nat.pos_of_dvd_of_pos divides positive
        have qposR : (0:ℚ) < (q:ℚ) := by exact_mod_cast qpos
        have mul : ((n/q : ℕ):ℚ)*(q:ℚ) = (n:ℚ) := by
          exact_mod_cast Nat.div_mul_cancel divides
        rw [(eq_div_iff (ne_of_gt qposR)).mpr mul, div_pow]
        ring
      _ ≤ (n:ℚ)^4 * 2 :=
        mul_le_mul_of_nonneg_left (reciprocal_divisors n positive) (by positivity)
      _ = 2*(n:ℚ)^4 := by ring
  exact_mod_cast bound

end OMA.DivisorFourthPowers

namespace OMA.DivisorFourthFinite

open OMA.S_oeis_a064377
open OMA.DivisorFourthTrial

private def entries : List ℕ := [2,3,4,6,8,10,12,14,15,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,48,50,54,56,60,66,70,72,78,80,84,90,96,100,102,108,110,114,120,126,130,132,138,140,144,150,156,162,168,174,180,186,192,198,204,210,216,222,228,234,240,246,252,258,264,270,276,282,294,300,306,312,330,336,342,360,378,390,396,420,450,462,480,504,510,540,546,570,600,630,660,690,714,720,750,780,840,870,930,990,1020,1050,1170,1260,1470,1680,2310]

private theorem entries_exact : entries.toFinset = listed := by decide +kernel

private theorem entries_small : ∀ n ∈ entries, n < 2311 := by decide +kernel

private def encode (xs : List ℕ) : ℕ :=
  xs.foldr (fun p tail => (1 <<< p) ||| tail) 0

private def digits : ℕ := 239491433657096539671551985506452637390459444705764855638224540397745680286664970589947164809211456920108884994803001093392043561257705233210873049985955712608931830297753099948630338090066515686273881133334072442113044093888490485386664029090230106895123864853998942267080990040542938607987678072348931101324673285086585931011637362419344919325428924111707300348177974046249646478736484482812464814964652794350331540101782284309167590207298831542910394503678658103706549387447564704552514532606544187783857210117951663918439870333984022035097433887644147595870684636555768546183449680980278301149787024118699536804935510453640301632758459771335963105064744566303338077625103188218295747882636636

private theorem digits_exact : digits = encode entries := by decide +kernel

private theorem encode_iff (xs : List ℕ) (n : ℕ) :
    (encode xs).testBit n = true ↔ n ∈ xs := by
  induction xs with
  | nil => simp [encode]
  | cons p rest ih =>
    change (((1 <<< p) ||| encode rest).testBit n = true) ↔ n ∈ p :: rest
    rw [Nat.testBit_lor, Bool.or_eq_true, ih]
    simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, eq_comm]

private theorem digits_iff (n : ℕ) : digits.testBit n = true ↔ n ∈ listed := by
  rw [digits_exact, encode_iff, ← entries_exact]
  exact List.mem_toFinset.symm

private def evaluated (n : ℕ) : Bool :=
  let f := (phi n)^5
  if 2*n^4 ≤ f then false else decide (f < sigmaFour n)

private theorem evaluated_iff (n : ℕ) (pos : 0 < n) (small : n < 5163) :
    evaluated n = true ↔ n.totient^5 < ∑ d ∈ n.divisors, d^4 := by
  by_cases clipped : 2*n^4 ≤ n.totient^5
  · have high := (OMA.DivisorFourthPowers.sigmaFour_le_two n pos).trans clipped
    simp [evaluated,phi_eq n pos small,clipped,not_lt.mpr high]
  · simp [evaluated,phi_eq n pos small,clipped,sigmaFour_eq n pos small]

private theorem at_window (start size n : ℕ)
    (checked : ∀ i : Fin size, evaluated (start+i.val) = digits.testBit (start+i.val))
    (lo : start ≤ n) (hi : n < start+size) :
    evaluated n = digits.testBit n := by
  have row := checked ⟨n-start,by omega⟩
  change evaluated (start+(n-start)) = digits.testBit (start+(n-start)) at row
  rwa [show start+(n-start)=n by omega] at row

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate0 : PLift (∀ j : Fin 512,
    evaluated (1+j.val) = digits.testBit (1+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate1 : PLift (∀ j : Fin 512,
    evaluated (513+j.val) = digits.testBit (513+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate2 : PLift (∀ j : Fin 512,
    evaluated (1025+j.val) = digits.testBit (1025+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate3 : PLift (∀ j : Fin 512,
    evaluated (1537+j.val) = digits.testBit (1537+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate4 : PLift (∀ j : Fin 512,
    evaluated (2049+j.val) = digits.testBit (2049+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate5 : PLift (∀ j : Fin 512,
    evaluated (2561+j.val) = digits.testBit (2561+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate6 : PLift (∀ j : Fin 512,
    evaluated (3073+j.val) = digits.testBit (3073+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate7 : PLift (∀ j : Fin 512,
    evaluated (3585+j.val) = digits.testBit (3585+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate8 : PLift (∀ j : Fin 512,
    evaluated (4097+j.val) = digits.testBit (4097+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate9 : PLift (∀ j : Fin 512,
    evaluated (4609+j.val) = digits.testBit (4609+j.val)) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def gate10 : PLift (∀ j : Fin 42,
    evaluated (5121+j.val) = digits.testBit (5121+j.val)) :=
  ⟨by decide +kernel⟩

private theorem checked_low (n : ℕ) (positive : 0 < n) (upper : n < 5163) :
    evaluated n = digits.testBit n := by
  by_cases h0 : n < 513
  · exact at_window 1 512 n gate0.down (by omega) h0
  by_cases h1 : n < 1025
  · exact at_window 513 512 n gate1.down (by omega) h1
  by_cases h2 : n < 1537
  · exact at_window 1025 512 n gate2.down (by omega) h2
  by_cases h3 : n < 2049
  · exact at_window 1537 512 n gate3.down (by omega) h3
  by_cases h4 : n < 2561
  · exact at_window 2049 512 n gate4.down (by omega) h4
  by_cases h5 : n < 3073
  · exact at_window 2561 512 n gate5.down (by omega) h5
  by_cases h6 : n < 3585
  · exact at_window 3073 512 n gate6.down (by omega) h6
  by_cases h7 : n < 4097
  · exact at_window 3585 512 n gate7.down (by omega) h7
  by_cases h8 : n < 4609
  · exact at_window 4097 512 n gate8.down (by omega) h8
  by_cases h9 : n < 5121
  · exact at_window 4609 512 n gate9.down (by omega) h9
  exact at_window 5121 42 n gate10.down (by omega) upper

theorem bounded (n : ℕ) (upper : n < 81920) (positive : 0 < n) :
    (n.totient^5 < ∑ d ∈ n.divisors, d^4) ↔ n ∈ listed := by
  by_cases small : n < 5163
  · rw [← evaluated_iff n positive small, checked_low n positive small, digits_iff]
  · have dominates := OMA.DivisorFourthRange.upper_exclusion n (by omega) upper
    have impossible := not_lt.mpr ((OMA.DivisorFourthPowers.sigmaFour_le_two n positive).trans dominates)
    have absent : n ∉ listed := by
      intro member
      have below := entries_small n (List.mem_toFinset.mp (entries_exact.symm ▸ member))
      omega
    simp [impossible,absent]

end OMA.DivisorFourthFinite

namespace OMA.A064377

open scoped BigOperators

private def allowance (p : ℕ) : ℕ :=
  if p = 2 then 512 else if p = 3 then 20 else if p = 5 then 2 else 1

private theorem allowance_pos (p : ℕ) : 1 ≤ allowance p := by
  unfold allowance
  split <;> try decide
  split <;> try decide
  split <;> decide

private theorem prime_bound (p : ℕ) (hp : p.Prime) : p^9 ≤ allowance p * (p-1)^10 := by
  by_cases small : p < 7
  · have finite : ∀ i : Fin 7, i.val.Prime →
        i.val^9 ≤ allowance i.val * (i.val-1)^10 := by decide +kernel
    exact finite ⟨p,small⟩ hp
  · have allow : allowance p = 1 := by
      simp [allowance, show p ≠ 2 by omega, show p ≠ 3 by omega, show p ≠ 5 by omega]
    rw [allow, one_mul]
    by_cases within : p < 513
    · have finite : ∀ i : Fin 513, 7 ≤ i.val → i.val^9 ≤ (i.val-1)^10 := by decide +kernel
      exact finite ⟨p,within⟩ (show 7 ≤ p by omega)
    · have upper : p ≤ 2*(p-1) := by omega
      have lower : (2:ℕ)^9 ≤ p-1 := by norm_num; omega
      calc
        p^9 ≤ (2*(p-1))^9 := Nat.pow_le_pow_left upper _
        _ = 2^9*(p-1)^9 := by rw [mul_pow]
        _ ≤ (p-1)*(p-1)^9 := Nat.mul_le_mul_right _ lower
        _ = (p-1)^10 := by ring

private theorem prime_power_bound (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    (p^e)^9 ≤ allowance p * (p^(e-1)*(p-1))^10 := by
  obtain ⟨k,rfl⟩ : ∃ k, e = k+1 := ⟨e-1, by omega⟩
  have hpow : (p^k)^9 ≤ (p^k)^10 := Nat.pow_le_pow_right (pow_pos hp.pos _) (by decide)
  calc
    (p^(k+1))^9 = (p^k)^9*p^9 := by rw [show p^(k+1) = p^k*p from pow_succ _ _, mul_pow]
    _ ≤ (p^k)^10*(allowance p*(p-1)^10) := Nat.mul_le_mul hpow (prime_bound p hp)
    _ = allowance p * (p^(k+1-1)*(p-1))^10 := by simp only [Nat.add_sub_cancel, mul_pow]; ring

private theorem prod_allowance (s : Finset ℕ) : ∏ p ∈ s, allowance p ≤ 20480 := by
  let exceptional : Finset ℕ := {2,3,5}
  calc
    (∏ p ∈ s, allowance p) = ∏ p ∈ s ∩ exceptional, allowance p := by
      symm
      apply Finset.prod_subset Finset.inter_subset_left
      intro p hp missing
      have h : p ∉ exceptional := fun hin => missing (Finset.mem_inter.mpr ⟨hp,hin⟩)
      have separate : p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 := by
        simpa [exceptional] using h
      simp [allowance, separate.1, separate.2.1, separate.2.2]
    _ ≤ ∏ p ∈ exceptional, allowance p :=
      Finset.prod_le_prod_of_subset_of_one_le' Finset.inter_subset_right (fun p _ _ => allowance_pos p)
    _ = 20480 := by decide +kernel

/-- A lower bound for the totient follows by multiplying the prime-power bounds. -/
theorem totient_bound (n : ℕ) (hn : n ≠ 0) : n^9 ≤ 20480*n.totient^10 := by
  let s := n.factorization.support
  have number : (∏ p ∈ s, p ^ n.factorization p) = n :=
    Nat.prod_factorization_pow_eq_self hn
  have totient : (∏ p ∈ s, p ^ (n.factorization p-1)*(p-1)) = n.totient :=
    (Nat.totient_eq_prod_factorization hn).symm
  calc
    n^9 = ∏ p ∈ s, (p^n.factorization p)^9 := by rw [Finset.prod_pow, number]
    _ ≤ ∏ p ∈ s, allowance p * (p^(n.factorization p-1)*(p-1))^10 := by
      apply Finset.prod_le_prod'
      intro p hp
      exact prime_power_bound p _ (Nat.prime_of_mem_primeFactors hp)
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))
    _ = (∏ p ∈ s, allowance p) * n.totient^10 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow, totient]
    _ ≤ 20480 * n.totient^10 := Nat.mul_le_mul_right _ (prod_allowance s)

theorem finite_bound (n : ℕ) (hn : n ≠ 0) (h : n.totient^5 < 2*n^4) : n < 81920 := by
  have squared := Nat.pow_lt_pow_left h (by decide : (2 : Nat) ≠ 0)
  have strict : n^9 < 81920*n^8 := calc
    n^9 ≤ 20480*n.totient^10 := totient_bound n hn
    _ = 20480*(n.totient^5)^2 := by ring
    _ < 20480*(2*n^4)^2 := Nat.mul_lt_mul_of_pos_left squared (by decide)
    _ = 81920*n^8 := by ring
  rw [show n^9 = n*n^8 by ring] at strict
  exact Nat.lt_of_mul_lt_mul_right strict

end OMA.A064377

open OMA.S_oeis_a064377 in
theorem OMA.solution : type_of% @OMA.S_oeis_a064377.main := by
  intro n positive
  by_cases finite : n < 81920
  · exact OMA.DivisorFourthFinite.bounded n finite positive
  · have not_lt : ¬ n.totient^5 < ∑ d ∈ n.divisors, d^4 := by
      intro h
      exact finite (OMA.A064377.finite_bound n (Nat.ne_of_gt positive)
        (h.trans_le (OMA.DivisorFourthPowers.sigmaFour_le_two n positive)))
    have not_mem : n ∉ listed := by
      intro member
      have below := OMA.DivisorFourthFinite.entries_small n (List.mem_toFinset.mp
        (OMA.DivisorFourthFinite.entries_exact.symm ▸ member))
      omega
    exact iff_of_false not_lt not_mem