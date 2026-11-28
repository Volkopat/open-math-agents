import OMAReductions.R_OeisA215926_conjecture_2_R1_H1_R1

/-! Necessary conditions on odd almost-perfect squares in the dyadic prime interval. -/
namespace OMA.R_OeisA215926_conjecture_2_R1_H1_R1_H1_R1

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem sigma_square (b : ℕ) (hb : Squarefree b) :
    σ 1 (b^2) = ∏ p ∈ b.primeFactors, (p^2+p+1) := by
  rw [sigma_one_apply, Nat.sum_divisors (pow_ne_zero _ hb.ne_zero),
    Nat.primeFactors_pow b (by decide : 2 ≠ 0)]
  apply prod_congr rfl
  intro p hp
  have he := Nat.factorization_eq_one_of_squarefree hb (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)
  rw [Nat.factorization_pow]
  simp [Finsupp.smul_apply,he,Finset.sum_range_succ]
  ring

theorem local_three (p : ℕ) :
    ∃ u : ℕ, (p^2+p+1) = (if p%3=1 then 3 else 1)*(3*u+1) := by
  rcases (show p%3=0 ∨ p%3=1 ∨ p%3=2 by omega) with h|h|h
  · obtain ⟨x,rfl⟩ : ∃ x, p=3*x := ⟨p/3,by omega⟩
    refine ⟨3*x^2+x,?_⟩
    rw [if_neg (by omega)]

    ring
  · obtain ⟨x,rfl⟩ : ∃ x, p=3*x+1 := ⟨p/3,by omega⟩
    refine ⟨x^2+x,?_⟩
    rw [if_pos h]

    ring
  · obtain ⟨x,rfl⟩ : ∃ x, p=3*x+2 := ⟨p/3,by omega⟩
    refine ⟨3*x^2+5*x+2,?_⟩
    rw [if_neg (by omega)]

    ring

theorem product_three (s : Finset ℕ) : ∃ u : ℕ,
    (∏ p ∈ s, (p^2+p+1)) = 3^(s.filter (fun p => p%3=1)).card*(3*u+1) := by
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨v,hv⟩ := local_three p
    obtain ⟨u,hu⟩ := ih
    refine ⟨3*v*u+v+u,?_⟩
    have hnot : p ∉ s.filter (fun p => p%3=1) := fun h => hp (mem_filter.mp h).1
    by_cases h : p%3=1
    · simp only [prod_insert hp,filter_insert,if_pos h,card_insert_of_notMem hnot]
      rw [pow_succ 3]
      rw [hu,hv,if_pos h]
      ring
    · simp only [prod_insert hp,filter_insert,if_neg h]
      rw [hu,hv,if_neg h]
      ring

theorem sigma_two (a : ℕ) : σ 1 (2^a)+1 = 2^(a+1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [Finset.sum_range_succ,pow_succ _ (a+1)]
    omega

theorem level_three (a b : ℕ) (hb : Squarefree b) (ho : Odd b)
    (h : σ 1 (2^a*b^2)+1 = 2*(2^a*b^2)) : ∃ u : ℕ,
    (2^(a+1)-1)*3^(b.primeFactors.filter (fun p => p%3=1)).card*(3*u+1)+1 =
        2^(a+1)*b^2 := by
  have co := (Nat.coprime_two_left.mpr ho).pow_left a |>.pow_right 2
  rw [isMultiplicative_sigma.map_mul_of_coprime co, sigma_square b hb] at h
  obtain ⟨u, hu⟩ := product_three b.primeFactors
  rw [hu] at h
  have e := sigma_two a
  refine ⟨u,?_⟩
  rw [show 2^(a+1)-1=σ 1 (2^a) by omega, mul_assoc _ _ (3*u+1)]
  simpa only [pow_succ, mul_comm (2^a) 2, mul_assoc] using h

private theorem pow_two_mod_three (a : ℕ) : 2^a%3=1 ∨ 2^a%3=2 := by
  induction a with
  | zero => decide
  | succ k ih =>
    rw [pow_succ,Nat.mul_mod]
    rcases ih with h|h <;> rw [h] <;> decide

theorem three_not_dvd (a b : ℕ) (hb : Squarefree b) (ho : Odd b)
    (h : σ 1 (2^a*b^2)+1 = 2*(2^a*b^2)) : ¬ 3 ∣ b := by
  obtain ⟨u,hu⟩ := level_three a b hb ho h
  intro hd
  let s := (b.primeFactors.filter (fun p => p%3=1)).card
  change (2^(a+1)-1)*3^s*(3*u+1)+1=2^(a+1)*b^2 at hu
  have hz : (2^(a+1)*b^2)%3=0 := Nat.mod_eq_zero_of_dvd
    (dvd_mul_of_dvd_right (dvd_pow hd (by decide : 2 ≠ 0)) _)
  have hm := congrArg (fun x : ℕ => x%3) hu
  change ((2^(a+1)-1)*3^s*(3*u+1)+1)%3=(2^(a+1)*b^2)%3 at hm
  rw [hz] at hm
  have tpos : 0 < 2^(a+1) := pow_pos (by decide) _
  rcases (pow_two_mod_three (a+1)) with h1|h2
  all_goals
    have hn : (2^(a+1)-1)%3 = 0 ∨ (2^(a+1)-1)%3=1 := by omega
    rcases s with _ | s
    · simp only [pow_zero,mul_one] at hm
      rw [Nat.add_mod,Nat.mul_mod,show (3*u+1)%3=1 by omega] at hm
      rcases hn with h|h <;> rw [h] at hm <;> contradiction
    · have hzero : 3 ∣ (2^(a+1)-1)*3^(s+1)*(3*u+1) :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega : s+1 ≠ 0)) _) _
      obtain ⟨w,hw⟩ := hzero
      rw [hw] at hm
      omega

theorem divisor_eight {q x : ℕ} (ho : Odd q) (h : 2*x^2 ≡ 1 [MOD q]) :
    q%8=1 ∨ q%8=7 := by
  have cast_h : (2*(x:ℤ)^2) ≡ 1 [ZMOD (q:ℤ)] := by exact_mod_cast h
  have j := jacobiSym.mod_left' cast_h
  rw [jacobiSym.mul_left,jacobiSym.pow_left,jacobiSym.one_left,
    jacobiSym.at_two ho,ZMod.χ₈_nat_eq_if_mod_eight] at j
  have odd : q%2 ≠ 0 := by have := Nat.odd_iff.mp ho; omega
  rw [if_neg odd] at j
  by_contra no
  rw [if_neg no] at j
  nlinarith [sq_nonneg (jacobiSym (x:ℤ) q)]

theorem prime_classes (v b p : ℕ) (hb : Squarefree b) (ho : Odd b) (hp : p ∈ b.primeFactors)
    (h : σ 1 (2^(2*v)*b^2)+1=2*(2^(2*v)*b^2)) : p%24=5 ∨ p%24=23 := by
  have hnp := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  have p_odd := ho.of_dvd_nat hdiv
  have p_pos := hnp.pos
  have hz := three_not_dvd (2*v) b hb ho h
  have co := (Nat.coprime_two_left.mpr ho).pow_left (2*v) |>.pow_right 2
  rw [isMultiplicative_sigma.map_mul_of_coprime co, sigma_square b hb] at h
  have factor : (p^2+p+1) ∣ σ 1 (2^(2*v))*(∏ q ∈ b.primeFactors,(q^2+q+1)) :=
    dvd_mul_of_dvd_right (dvd_prod_of_mem _ hp) _
  obtain ⟨w,hw⟩ := factor
  have eqn : 2*(2^v*b)^2 = 1 + (p^2+p+1)*w := by
    rw [show 2^(2*v)= (2^v)^2 by rw [mul_comm 2 v,pow_mul]] at h hw
    linear_combination (norm := ring) -h+hw
  have red (q : ℕ) (hq : q ∣ (p^2+p+1)) : 2*(2^v*b)^2 ≡ 1 [MOD q] := by
    rw [eqn]
    exact (Nat.modEq_iff_dvd' (by omega)).mpr (by simpa using dvd_mul_of_dvd_left hq w) |>.symm
  have phi_odd : Odd ((p^2+p+1)) := by exact (p_odd.pow.add_odd p_odd).add_one
  have eight := divisor_eight phi_odd (red _ dvd_rfl)
  have no_one : p%3 ≠ 1 := by
    intro h1
    have qt : 3 ∣ (p^2+p+1) := by
      obtain ⟨u,hu⟩ := local_three p
      rw [hu,if_pos h1]
      exact dvd_mul_right _ _
    have absurd := divisor_eight (by decide : Odd 3) (red 3 qt)
    omega
  have no_zero : p%3 ≠ 0 := fun h0 => hz ((Nat.dvd_of_mod_eq_zero h0).trans hdiv)
  have psq : p^2%8=1 := by
    have odd := Nat.odd_iff.mp p_odd
    rw [pow_two, Nat.mul_mod]
    rcases (show p%8=1 ∨ p%8=3 ∨ p%8=5 ∨ p%8=7 by omega) with h|h|h|h <;> rw [h]
  have hphi : (p^2+p+1) % 8 = (p+2)%8 := by
    omega
  rw [hphi] at eight
  omega

private theorem ratio_ge (p : ℕ) : 1 ≤ ((1:ℚ)+1/(p:ℚ)+1/(p:ℚ)^2) := by
  have h : 0 ≤ (1:ℚ)/p := by positivity
  have h' : 0 ≤ (1:ℚ)/(p:ℚ)^2 := by positivity
  linarith

private theorem ratio_anti {p q : ℕ} (hp : 0 < p) (h : p ≤ q) : ((1:ℚ)+1/(q:ℚ)+1/(q:ℚ)^2) ≤ ((1:ℚ)+1/(p:ℚ)+1/(p:ℚ)^2) := by
  have h' : (p:ℚ) ≤ (q:ℚ) := by exact_mod_cast h
  have hpos : 0 < (p:ℚ) := by exact_mod_cast hp
  have sq : (p:ℚ)^2 ≤ (q:ℚ)^2 := by gcongr

  linarith [one_div_le_one_div_of_le hpos h',
    one_div_le_one_div_of_le (sq_pos_of_pos hpos) sq]

private theorem sigma_ratio (b : ℕ) (hb : Squarefree b) :
    ((σ 1 (b^2):ℕ):ℚ) = (b:ℚ)^2 * ∏ p ∈ b.primeFactors, ((1:ℚ)+1/(p:ℚ)+1/(p:ℚ)^2) := by
  have bigint := congrArg (fun t : ℕ => (t:ℚ)) (Nat.prod_primeFactors_of_squarefree hb)
  change ((∏ p ∈ b.primeFactors, p : ℕ):ℚ) = (b:ℚ) at bigint
  rw [Nat.cast_prod] at bigint
  rw [sigma_square b hb, Nat.cast_prod]
  calc
    _ = ∏ p ∈ b.primeFactors, (p:ℚ)^2*((1:ℚ)+1/(p:ℚ)+1/(p:ℚ)^2) := by
      apply prod_congr rfl
      intro p hp
      have pos := (Nat.prime_of_mem_primeFactors hp).pos
      have hn : (p:ℚ) ≠ 0 := by exact_mod_cast pos.ne'
      push_cast
      field_simp
    _ = _ := by rw [prod_mul_distrib,Finset.prod_pow,bigint]

/-- Bound the Euler product by using all admissible primes below a cutoff
and the largest possible factor above the cutoff. -/
private theorem count_upper (S : Finset ℕ) (bound N : ℕ)
    (admiss : ∀ p ∈ S, p.Prime ∧ (p%24=5 ∨ p%24=23)) (hc : S.card ≤ N) :
    let r := fun p : ℕ => (1:ℚ) + 1/p + 1/(p:ℚ)^2
    let small := (range (bound+1)).filter (fun p => p.Prime ∧ (p%24=5 ∨ p%24=23))
    (∏ p ∈ S, r p) ≤ (∏ p ∈ small, r p) * r (bound+1)^N := by
  let r := fun p : ℕ => (1:ℚ) + 1/p + 1/(p:ℚ)^2
  let small := (range (bound+1)).filter (fun p => p.Prime ∧ (p%24=5 ∨ p%24=23))
  change (∏ p ∈ S, r p) ≤ (∏ p ∈ small, r p) * r (bound+1)^N
  let F := S.filter (fun p => p≤bound)
  have fs : F ⊆ S := filter_subset _ _
  have ft : F ⊆ small := by
    intro p hp
    obtain ⟨hs,hb⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),admiss p hs⟩
  have pos (p : ℕ) : 0 ≤ r p := zero_le_one.trans (ratio_ge p)
  have low := Finset.prod_le_prod_of_subset_of_one_le (f:=r) ft
    (fun p _ => pos p) (fun p _ _ => ratio_ge p)
  have high : (∏ p ∈ S \ F, r p) ≤ r (bound+1)^N := by
    calc
      _ ≤ ∏ _p ∈ S \ F, r (bound+1) := by
        apply prod_le_prod (fun p _ => pos p)
        intro p hp
        obtain ⟨hs,hn⟩ := mem_sdiff.mp hp
        have large : bound < p := lt_of_not_ge (fun g => hn (mem_filter.mpr ⟨hs,g⟩))
        exact ratio_anti (by omega) large
      _ = r (bound+1)^(S \ F).card := by simp
      _ ≤ _ := pow_le_pow_right₀ (ratio_ge _) ((card_le_card sdiff_subset).trans hc)
  rw [←prod_sdiff fs (f:=r),mul_comm (∏ p ∈ S \ F, r p)]
  exact mul_le_mul low high (prod_nonneg (fun p _ => pos p)) (prod_nonneg (fun p _ => pos p))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
private theorem bound_1000 :
    let r := fun p : ℕ => (1:ℚ) + 1/p + 1/(p:ℚ)^2
    let small := (range 1001).filter (fun p => p.Prime ∧ (p%24=5 ∨ p%24=23))
    (∏ p ∈ small, r p) * r 1001^222 < (49:ℚ)/25 := by
  let r := fun p : ℕ => (1:ℚ) + 1/p + 1/(p:ℚ)^2
  let small := (range 1001).filter (fun p => p.Prime ∧ (p%24=5 ∨ p%24=23))
  let allowed : Finset ℕ :=
    {5,23,29,47,53,71,101,149,167,173,191,197,239,263,269,293,311,317,359,383,
     389,431,461,479,503,509,557,599,647,653,677,701,719,743,773,797,821,839,863,
     887,911,941,983}
  change (∏ p ∈ small, r p) * r 1001^222 < (49:ℚ)/25
  have cover : small ⊆ allowed := by
    intro p hm
    obtain ⟨hlt,hp,mod⟩ := mem_filter.mp hm
    have hle := mem_range.mp hlt
    have split : p=24*(p/24)+5 ∨ p=24*(p/24)+23 := by omega
    generalize e : p/24=t at split
    have tbound : t ≤ 41 := by omega
    rcases split with h|h <;> subst p <;> interval_cases t <;>
      first | omega | decide +kernel | norm_num at hp
  have prod_le := Finset.prod_le_prod_of_subset_of_one_le (f:=r) cover
    (fun p _ => zero_le_one.trans (ratio_ge p)) (fun p _ _ => ratio_ge p)
  calc
    _ ≤ (∏ p ∈ allowed, r p) * r 1001^222 :=
      mul_le_mul_of_nonneg_right prod_le (pow_nonneg (zero_le_one.trans (ratio_ge _)) _)
    _ < _ := by norm_num [allowed,r,Finset.prod_insert]

theorem odd_squarefree_count (b : ℕ) (hb : Squarefree b) (ho : Odd b) (nontriv : 1<b)
    (h : σ 1 (b^2)+1=2*b^2) : 223 ≤ b.primeFactors.card := by
  by_contra! small
  have h0 : σ 1 (2^(2*0)*b^2)+1=2*(2^(2*0)*b^2) := by simpa using h
  have hz := three_not_dvd 0 b hb ho (by simpa using h)
  have b5 : 5 ≤ b := by have := Nat.odd_iff.mp ho; omega
  have hbound := (count_upper b.primeFactors 1000 222
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,prime_classes 0 b p hb ho hp h0⟩) (by omega)).trans_lt bound_1000
  have bpos : (0:ℚ) < b := by exact_mod_cast (show 0<b by omega)
  have hard := mul_lt_mul_of_pos_left hbound (sq_pos_of_pos bpos)
  rw [←sigma_ratio b hb] at hard
  have exact_h : ((σ 1 (b^2):ℕ):ℚ)+1=2*(b:ℚ)^2 := by exact_mod_cast h
  have b5' : (5:ℚ) ≤ b := by exact_mod_cast b5
  nlinarith [mul_nonneg (sub_nonneg.mpr b5') (show (0:ℚ) ≤ b+5 by positivity)]

private theorem root_lower_bound (b : ℕ) (hs : Squarefree b)
    (hc : 223 ≤ b.primeFactors.card)
    (cl : ∀ p ∈ b.primeFactors, p%24=5 ∨ p%24=23) : 23^222 ≤ b := by
  have he : 222 ≤ (b.primeFactors.erase 5).card := by
    by_cases h : 5 ∈ b.primeFactors
    · rw [card_erase_of_mem h]
      omega
    · rw [erase_eq_of_notMem h]
      omega
  calc
    23^222 ≤ 23^(b.primeFactors.erase 5).card := Nat.pow_le_pow_right (by decide) he
    _ = ∏ _p ∈ b.primeFactors.erase 5, 23 := by simp
    _ ≤ ∏ p ∈ b.primeFactors.erase 5, p := by
      apply prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      obtain ⟨hne,hm⟩ := mem_erase.mp hp
      have := cl p hm
      omega
    _ ≤ ∏ p ∈ b.primeFactors, p :=
      prod_le_prod_of_subset_of_one_le (f:=fun p : ℕ => p) (erase_subset _ _)
        (fun _ _ => Nat.zero_le _) (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_le)
    _ = b := Nat.prod_primeFactors_of_squarefree hs

private theorem local_divisor_eight (b p d : ℕ) (hb : b ≠ 0) (hp : p ∈ b.primeFactors)
    (h : σ 1 (b^2)+1 = 2*b^2)
    (hd : d ∣ ∑ j ∈ range (2*b.factorization p+1), p^j) : d%8=1 ∨ d%8=7 := by
  have product : σ 1 (b^2) =
      ∏ r ∈ b.primeFactors, ∑ j ∈ range (2*b.factorization r+1), r^j := by
    rw [sigma_one_apply,Nat.sum_divisors (pow_ne_zero _ hb),Nat.primeFactors_pow _ (by decide : 2≠0)]
    simp [Nat.factorization_pow,Finsupp.smul_apply]
  have full : d ∣ σ 1 (b^2) := by
    rw [product]
    exact hd.trans (dvd_prod_of_mem _ hp)
  have odd_sum : Odd (σ 1 (b^2)) := Nat.odd_iff.mpr (by omega)
  have odd_d := odd_sum.of_dvd_nat full
  obtain ⟨u,hu⟩ := full
  have eqn : 2*b^2 = 1+d*u := by omega
  apply divisor_eight odd_d (x:=b)
  rw [eqn]
  exact (Nat.modEq_iff_dvd' (by omega)).mpr (by simp) |>.symm

/-- A squarefree root must have at least 223 distinct prime divisors, each
congruent to 5 or 23 modulo 24. At most one can be 5. -/
def H1 : Prop :=
  ∀ b : ℕ, Odd b → Squarefree b → 23^222 ≤ b → 223 ≤ b.primeFactors.card →
    (∀ p ∈ b.primeFactors, p%24=5 ∨ p%24=23) → σ 1 (b^2)+1=2*b^2 →
    ∀ q : ℕ, q.Prime → 2^((b^2).log2+1) < q → 2*b^2 ≤ q

/-- For a root with a repeated prime factor, every divisor of every local
geometric sum must lie in one of two residue classes modulo 8. -/
def H2 : Prop :=
  ∀ b : ℕ, Odd b → 257 ≤ b → ¬ Squarefree b →
    (∀ p e : ℕ, p.Prime → 0 < e → b ≠ p^e) →
    (∀ p ∈ b.primeFactors, ∀ d : ℕ,
      d ∣ ∑ j ∈ range (2*b.factorization p+1), p^j → d%8=1 ∨ d%8=7) →
    σ 1 (b^2)+1=2*b^2 →
    ∀ q : ℕ, q.Prime → 2^((b^2).log2+1) < q → 2*b^2 ≤ q

theorem main : H1 → H2 → OMA.R_OeisA215926_conjecture_2_R1_H1_R1.H1 := by
  intro square repeated b ho hl hnot h
  by_cases hs : Squarefree b
  · have c := odd_squarefree_count b hs ho (by omega) h
    have base : σ 1 (2^(2*0)*b^2)+1=2*(2^(2*0)*b^2) := by simpa using h
    have cl (p : ℕ) (hp : p ∈ b.primeFactors) := prime_classes 0 b p hs ho hp base
    exact square b ho hs (root_lower_bound b hs c cl) c cl h
  · exact repeated b ho hl hs hnot (fun p hp d hd =>
      local_divisor_eight b p d (by omega) hp h hd) h

end OMA.R_OeisA215926_conjecture_2_R1_H1_R1_H1_R1
