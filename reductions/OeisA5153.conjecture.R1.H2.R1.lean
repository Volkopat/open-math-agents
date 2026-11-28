import OMAReductions.R_OeisA5153_conjecture_R1
/-! Practical differences via binary remainders and the exact sorted-divisor gap test. Credit: @AlfredMelson. -/
namespace OMA.R_OeisA5153_conjecture_R1_H2_R1
open Finset

private theorem cover {s : Finset ℕ}
    (H : ∀ d ∈ s, d ≤ (∑ t ∈ s.filter (· < d), t)+1) :
    ∀ x ≤ ∑ t ∈ s, t, x ∈ subsetSums (s : Set ℕ) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    have hlt : (insert a s).filter (· < a) = s := by ext z; simp; grind
    have hcap := H a (mem_insert_self ..)
    rw [hlt] at hcap
    have old := ih (fun d hd => by
      have h := H d (mem_insert_of_mem hd)
      simpa [filter_insert, not_lt.mpr (hmax d hd).le] using h)
    intro x hx
    rw [sum_insert ha] at hx
    by_cases small : x ≤ ∑ t ∈ s, t
    · exact subsetSums_mono (by simp) (old x small)
    · obtain ⟨B,hB,hx'⟩ := old (x-a) (by omega)
      have hab : a ∉ B := fun h => ha (hB h)
      exact ⟨insert a B, by simpa only [Finset.coe_insert] using Set.insert_subset_insert hB, by rw [sum_insert hab, ← hx']; omega⟩

theorem noGap_iff {q : ℕ} (hq : 0<q) : (∀ d ∈ (q : ℕ).divisors, d ≤ (∑ t ∈ (q : ℕ).divisors.filter (· < d), t)+1) ↔ Nat.IsPractical q := by
  constructor
  · intro h x hx
    exact cover h x (hx.trans (Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self q hq.ne')))
  · intro h d hd
    by_contra! bad
    let s := q.divisors.filter (· < d)
    let x := (∑ t ∈ s, t)+1
    have hxd : x < d := bad
    obtain ⟨B,hB,hx⟩ := h x (hxd.le.trans (Nat.le_of_dvd hq (Nat.mem_divisors.mp hd).1))
    have sub : B ⊆ s := by
      intro t ht
      exact mem_filter.mpr ⟨hB ht, lt_of_le_of_lt (hx ▸ single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ht) hxd⟩
    have le := Finset.sum_le_sum_of_subset_of_nonneg (f := id) sub (by intros; omega)
    change (∑ t ∈ B,t) ≤ ∑ t ∈ s,t at le
    dsimp [x] at hx
    omega

/-- Binary digits use only divisors of the base power of two. -/
private theorem binary (k x : ℕ) (hx : x < 2^(k+1)) :
    x ∈ subsetSums ((2^k : ℕ).divisors : Set ℕ) := by
  induction k generalizing x with
  | zero =>
    interval_cases x <;> first | exact zero_mem_subsetSums _ | exact ⟨{1}, by simp, by simp⟩
  | succ k ih =>
    have hp : 0 < 2^k := by positivity
    let t := 2^(k+1)
    have ht : 0<t := by dsimp [t]; positivity
    have lift : (((2^k : ℕ).divisors : Finset ℕ) : Set ℕ) ⊆ (t.divisors : Set ℕ) := by
      intro i hi
      exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hi).1.trans (by dsimp [t]; exact pow_dvd_pow _ (by omega)),ht.ne'⟩
    by_cases low : x < t
    · exact subsetSums_mono lift (ih x low)
    · rw [pow_succ] at hx
      obtain ⟨B,hB,hx'⟩ := ih (x-t) (by change x < t*2 at hx; omega)
      have out : t ∉ B := by
        intro h
        have hle := Nat.le_of_dvd hp (Nat.mem_divisors.mp (hB h)).1
        dsimp [t] at hle
        rw [pow_succ] at hle
        omega
      refine ⟨insert t B, ?_, ?_⟩
      · rw [coe_insert,Set.insert_subset_iff]
        exact ⟨Nat.mem_divisors_self _ ht.ne', hB.trans lift⟩
      · rw [sum_insert out, ← hx']; omega

/-- Bounded odd prime factors can be adjoined repeatedly, even if they
already divide the current number. The binary remainder uses no multiple of p. -/
private theorem extend {k q p : ℕ} (hq : 0 < q) (base : 2^k ∣ q)
    (pr : p.Prime) (odd : p ≠ 2) (lim : p ≤ 2^(k+1))
    (good : Nat.IsPractical q) : Nat.IsPractical (p*q) := by
  intro x hx
  obtain ⟨A,hA,ha⟩ := binary k (x%p) ((Nat.mod_lt _ pr.pos).trans_le lim)
  obtain ⟨B,hB,hb⟩ := good (x/p) ((Nat.div_le_div_right hx).trans (by rw [Nat.mul_div_cancel_left _ pr.pos]))
  let T := B.image (p*·)
  have nz : p*q ≠ 0 := Nat.mul_ne_zero pr.ne_zero hq.ne'
  have inj : Set.InjOn (p*·) (B : Set ℕ) := fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left pr.pos h
  have dis : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro i hi ht
    obtain ⟨j,_,rfl⟩ := mem_image.mp ht
    have dp : p ∣ 2^k := (dvd_mul_right p j).trans (Nat.mem_divisors.mp (hA hi)).1
    exact odd ((Nat.prime_dvd_prime_iff_eq pr Nat.prime_two).mp (pr.dvd_of_dvd_pow dp))
  refine ⟨A ∪ T, ?_, ?_⟩
  · intro i hi
    rcases mem_union.mp hi with h|h
    · exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp (hA h)).1.trans (base.trans (dvd_mul_left ..)),nz⟩
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left _ (Nat.mem_divisors.mp (hB hj)).1,nz⟩
  · rw [sum_union dis, show (∑ i ∈ T,i) = p*(x/p) by dsimp [T]; rw [sum_image inj, ← Finset.mul_sum, ← hb]]
    rw [← ha, Nat.mod_add_div]

theorem practical_smooth {k m : ℕ} (hm : 0 < m) (ho : Odd m)
    (smooth : ∀ p : ℕ, p.Prime → p ∣ m → p ≤ 2^(k+1)) :
    Nat.IsPractical (2^k*m) := by
  let L := m.primeFactorsList
  have prodL : L.prod=m := Nat.prod_primeFactorsList hm.ne'
  have all : ∀ p ∈ L, p.Prime ∧ p≠2 ∧ p≤2^(k+1) := by
    intro p hp
    have prime := Nat.prime_of_mem_primeFactorsList hp
    have dvd := Nat.dvd_of_mem_primeFactorsList hp
    exact ⟨prime,fun he => by subst p; obtain ⟨b,hb⟩ := ho; omega, smooth p prime dvd⟩
  rw [← prodL]
  suffices aux : ∀ l : List ℕ, (∀ p ∈ l, p.Prime ∧ p≠2 ∧ p≤2^(k+1)) →
      Nat.IsPractical (2^k*l.prod) from aux L all
  intro l
  induction l with
  | nil =>
    intro _
    simp only [List.prod_nil,mul_one]
    intro x hx
    apply binary
    rw [pow_succ]; have : 0 < 2^k := by positivity
    omega
  | cons p l ih =>
    intro props
    obtain ⟨hp,h2,hle⟩ := props p (by simp)
    have good := ih (fun t ht => props t (List.mem_cons_of_mem _ ht))
    have hpos : 0 < l.prod := List.prod_pos (fun t ht => (props t (List.mem_cons_of_mem _ ht)).1.pos)
    simpa only [List.prod_cons, mul_left_comm] using
      extend (k:=k) (q:=2^k*l.prod) (by positivity) (dvd_mul_right ..) hp h2 hle good

/-- Any practical q at least four is a multiple of three or four. -/
theorem three_or_four {q : ℕ} (hq : 4≤q) (h : Nat.IsPractical q) : 3∣q ∨ 4∣q := by
  by_contra! bad
  obtain ⟨B,hB,hs⟩ := h 4 hq
  have sub : B ⊆ {1,2} := by
    intro t ht
    obtain ⟨hd,hn⟩ := Nat.mem_divisors.mp (hB ht)
    have ht4 := Finset.single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) ht
    change t ≤ ∑ i ∈ B,i at ht4
    rw [← hs] at ht4
    interval_cases t <;> simp_all
  have := Finset.sum_le_sum_of_subset_of_nonneg (f:=id) sub (by intros; omega)
  norm_num at this
  omega

theorem tail_iff {q k : ℕ} (hq : 0 < q) (base : 2^k ∣ q) :
    (∀ d ∈ (q : ℕ).divisors, 2^(k+1) < d →
      d ≤ (∑ t ∈ (q : ℕ).divisors.filter (· < d), t)+1) ↔ Nat.IsPractical q := by
  rw [← noGap_iff hq]
  refine ⟨fun H d hd => ?_, fun H d hd _ => H d hd⟩
  by_cases big : 2^(k+1) < d
  · exact H d hd big
  have pos : 0 < d := Nat.pos_of_mem_divisors hd
  obtain ⟨B,hB,hs⟩ := binary k (d-1) (by omega)
  have sub : B ⊆ q.divisors.filter (· < d) := by
    intro t ht
    have le := single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) ht
    change t ≤ ∑ i ∈ B,i at le
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp (hB ht)).1.trans base,hq.ne'⟩,by omega⟩
  have le := Finset.sum_le_sum_of_subset_of_nonneg (f:=id) sub (by intros; omega)
  change (∑ i ∈ B,i) ≤ ∑ t ∈ q.divisors.filter (· < d), t at le
  omega

/-- The congruence restriction in the multiple-of-three branch is necessary
once the prime 3 and the already handled tiny differences are removed. -/
theorem four_dvd_difference {n p : ℕ} (three : 3 ∣ n) (hp : p.Prime)
    (other : p ≠ 3) (lt : p < n) (size : 4 ≤ n-p) (good : Nat.IsPractical (n-p)) :
    4 ∣ n-p := by
  rcases three_or_four size good with h|h
  · have dp : 3 ∣ p := by omega
    exact (other ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp dp).symm).elim
  · exact h

/-- When three divides n, after the prime 3 fails, the shifted prime
must lie in n's class modulo four. Only large divisor gaps need testing. -/
def H1 : Prop := ∀ n : ℕ, 7 ≤ n → Odd n → 3 ∣ n →
    ¬ (∃ p k m : ℕ, p.Prime ∧ 0 < m ∧ Odd m ∧ n=p+2^k*m ∧
      ∀ r : ℕ, r.Prime → r ∣ m → r ≤ 2^(k+1)) → ¬ (∀ d ∈ ((n-3) : ℕ).divisors, d ≤ (∑ t ∈ ((n-3) : ℕ).divisors.filter (· < d), t)+1) →
    ∃ p k : ℕ, p.Prime ∧ p < n ∧ 2 ≤ k ∧ 2^k ∣ n-p ∧ (∀ d ∈ ((n-p) : ℕ).divisors, 2^(k+1) < d →
      d ≤ (∑ t ∈ ((n-p) : ℕ).divisors.filter (· < d), t)+1)

/-- For n prime to three one can additionally use primes in n's class
modulo three, including when the difference is twice an odd number. -/
def H2 : Prop := ∀ n : ℕ, 7 ≤ n → Odd n → ¬ 3 ∣ n →
    ¬ (∃ p k m : ℕ, p.Prime ∧ 0 < m ∧ Odd m ∧ n=p+2^k*m ∧
      ∀ r : ℕ, r.Prime → r ∣ m → r ≤ 2^(k+1)) → ¬ (∀ d ∈ ((n-3) : ℕ).divisors, d ≤ (∑ t ∈ ((n-3) : ℕ).divisors.filter (· < d), t)+1) →
    ∃ p k : ℕ, p.Prime ∧ p < n ∧ (2 ≤ k ∨ 3 ∣ n-p) ∧ 2^k ∣ n-p ∧ (∀ d ∈ ((n-p) : ℕ).divisors, 2^(k+1) < d →
      d ≤ (∑ t ∈ ((n-p) : ℕ).divisors.filter (· < d), t)+1)

theorem main : H1 → H2 → OMA.R_OeisA5153_conjecture_R1.H2 := by
  intro h1 h2 n hn odd excluded
  have seven : 7 ≤ n := by
    by_contra! small
    obtain ⟨j,hj⟩ := odd
    rcases (show n=3 ∨ n=5 by omega) with h|h <;> rw [h] at excluded
    · exact (excluded 0).1 (by decide)
    · exact (excluded 1).1 (by decide)
  by_cases sm : (∃ p k m : ℕ, p.Prime ∧ 0 < m ∧ Odd m ∧ n=p+2^k*m ∧
      ∀ r : ℕ, r.Prime → r ∣ m → r ≤ 2^(k+1))
  · obtain ⟨p,k,m,hp,hm,ho,he,hs⟩ := sm
    exact ⟨p,2^k*m,hp,⟨by positivity, practical_smooth hm ho hs⟩,he⟩
  by_cases gap : (∀ d ∈ ((n-3) : ℕ).divisors, d ≤ (∑ t ∈ ((n-3) : ℕ).divisors.filter (· < d), t)+1)
  · exact ⟨3,n-3,by decide,⟨by omega,(noGap_iff (by omega)).mp gap⟩,by omega⟩
  have find : ∃ p k : ℕ, p.Prime ∧ p < n ∧ 2^k ∣ n-p ∧ (∀ d ∈ ((n-p) : ℕ).divisors, 2^(k+1) < d →
      d ≤ (∑ t ∈ ((n-p) : ℕ).divisors.filter (· < d), t)+1) := by
    by_cases three : 3 ∣ n
    · obtain ⟨p,k,hp,lt,_,base,t⟩ := h1 n seven odd three sm gap
      exact ⟨p,k,hp,lt,base,t⟩
    · obtain ⟨p,k,hp,lt,_,base,t⟩ := h2 n seven odd three sm gap
      exact ⟨p,k,hp,lt,base,t⟩
  obtain ⟨p,k,hp,lt,base,t⟩ := find
  exact ⟨p,n-p,hp,⟨by omega,(tail_iff (by omega) base).mp t⟩,by omega⟩

end OMA.R_OeisA5153_conjecture_R1_H2_R1
