import OMAReductions.R_Erdos373_erdos_373_variants_maximal_solution_R1
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Tactic.NormNum

namespace HickersonBudget

private lemma factorCost : ∀ a : ℕ, 2^(a/2) ∣ a.factorial
  | 0 => by decide
  | 1 => by decide
  | a+2 => by
    have htwo : 2 ∣ (a+2)*(a+1) := by
      rcases (show 2 ∣ a+2 ∨ 2 ∣ a+1 by omega) with he | he
      · exact dvd_mul_of_dvd_left he _
      · exact dvd_mul_of_dvd_right he _
    rw [show (a+2)/2 = a/2+1 by omega, pow_succ, Nat.factorial_succ, Nat.factorial_succ]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (Nat.mul_dvd_mul (factorCost a) htwo)

private lemma totalCost (l : List ℕ) : 2^(((l.map (· / 2)).sum)) ∣ (l.map Nat.factorial).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change 2^(a/2+((l.map (· / 2)).sum)) ∣ a.factorial * (l.map Nat.factorial).prod
    rw [pow_add]
    exact Nat.mul_dvd_mul (factorCost a) ih

private lemma lengthCost {l : List ℕ} (h : ∀ a ∈ l, 1 < a) : l.length ≤ ((l.map (· / 2)).sum) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    change l.length + 1 ≤ a/2 + ((l.map (· / 2)).sum)
    omega

private lemma cost_of_mem {a : ℕ} : ∀ (l : List ℕ), a ∈ l → a/2 ≤ (l.map (· / 2)).sum
  | [], ha => by simp at ha
  | b :: l, ha => by
    change a/2 ≤ b/2 + (l.map (· / 2)).sum
    rcases List.mem_cons.mp ha with rfl | ht
    · omega
    · have := cost_of_mem l ht; omega

theorem gapTwo_large_divisor (n : ℕ) (l : List ℕ) (hl : l.Pairwise (· ≥ ·))
    (hmin : ∀ a ∈ l, 1 < a) (hprod : n*(n-1) = (l.map Nat.factorial).prod)
    (hn : 16 < n) : 2^13 ∣ n*(n-1) := by
  let safe (x : ℕ) : Bool :=
    decide (Nat.sqrt (4*x+1) ≤ 31 ∨ (Nat.sqrt (4*x+1))^2 ≠ 4*x+1)
  let verify : ℕ → ℕ → ℕ → ℕ → Bool := Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool) (fun _ _ x => safe x)
    (fun _ previous b cap x => safe x &&
      (List.range (min cap (2*b+1)-1)).all fun j =>
        let a := j+2
        previous (b-a/2) a (x*a.factorial))
  have terminationCheck (f b cap x : ℕ) (h : verify f b cap x = true) : safe x = true := by
    cases f with
    | zero => exact h
    | succ f => exact (Bool.and_eq_true_iff.mp h).1

  have verification (l : List ℕ) (f b cap x : ℕ)
      (tested : verify f b cap x = true) (hf : l.length ≤ f) (hb : ((l.map (· / 2)).sum) ≤ b)
      (hlo : ∀ a ∈ l, 1 < a) (hhi : ∀ a ∈ l, a ≤ cap) (hs : l.Pairwise (· ≥ ·)) :
      safe (x*(l.map Nat.factorial).prod) = true := by
    induction l generalizing f b cap x with
    | nil => simpa using terminationCheck f b cap x tested
    | cons a l ih =>
      obtain ⟨f,rfl⟩ : ∃ k, f = k+1 := ⟨f-1, by simp at hf; omega⟩
      have ha := hlo a (by simp)
      have hau := hhi a (by simp)
      change a/2 + ((l.map (· / 2)).sum) ≤ b at hb
      have hj : a-2 ∈ List.range (min cap (2*b+1)-1) := by
        rw [List.mem_range]; omega
      have hit := List.all_eq_true.mp (Bool.and_eq_true_iff.mp tested).2 (a-2) hj
      have heq : a-2+2 = a := by omega
      simp only [heq] at hit
      have res := ih f (b-a/2) a (x*a.factorial) hit (by simpa using hf) (by omega)
        (fun q hq => hlo q (by simp [hq])) (List.pairwise_cons.mp hs).1 (List.pairwise_cons.mp hs).2
      simpa [Nat.mul_assoc] using res

  have safe_triangular (n : ℕ) (h : safe (n*(n-1)) = true) : n ≤ 16 := by
    cases n with
    | zero => decide
    | succ n =>
      have he : 4*((n+1)*n)+1 = (2*n+1)^2 := by ring
      simp [safe, he, Nat.sqrt_eq'] at h
      omega

  have verified_budget : verify 12 12 25 1 = true := by
    dsimp only [verify, safe]
    decide +kernel

  by_contra fail
  have lc : ((l.map (· / 2)).sum) ≤ 12 := by
    by_contra! h
    exact fail (hprod.symm ▸ dvd_trans (pow_dvd_pow 2 (by omega : 13 ≤ ((l.map (· / 2)).sum))) (totalCost l))
  have hh : ∀ a ∈ l, a ≤ 25 := by
    intro a ha
    have hc : a/2 ≤ ((l.map (· / 2)).sum) := by
      exact cost_of_mem l ha
    omega
  have hs := verification l 12 12 25 1 verified_budget ((lengthCost hmin).trans lc) lc hmin hh hl
  have := safe_triangular n (by simpa [hprod] using hs)
  omega

theorem prime_factorial_dvd (l : List ℕ) (p : ℕ) (prime : p.Prime)
    (h : p ∣ (l.map Nat.factorial).prod) : p.factorial ∣ (l.map Nat.factorial).prod := by
  induction l with
  | nil =>
    exact False.elim (prime.not_dvd_one (by simpa using h))
  | cons a l ih =>
    change p ∣ a.factorial * (l.map Nat.factorial).prod at h
    change p.factorial ∣ a.factorial * (l.map Nat.factorial).prod
    rcases prime.dvd_mul.mp h with ha | hl
    · exact dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial (prime.dvd_factorial.mp ha)) _
    · exact dvd_mul_of_dvd_right (ih hl) _

end HickersonBudget


namespace HickersonRange

lemma smooth_exclusion (n : ℕ) (lo : 16 < n) (hi : n ≤ 10000000)
    (hdiv : 8192 ∣ n*(n-1)) :
    ¬ (∀ p : ℕ, p.Prime → p ∣ n*(n-1) → p.factorial ∣ n*(n-1)) := by
  let good (m : ℕ) :=
    let u := m*(m-1)
    let q := u / Nat.gcd u (30030^48)
    decide (1 < q ∧ q ∣ u ∧ q.Coprime 30030)
  have cert : (List.range 1220).all (fun j =>
      good (8192*(j+1)) && good (8192*(j+1)+1)) = true := by
    dsimp only [good]
    decide +kernel
  have par : 8192 ∣ n ∨ 8192 ∣ n-1 := by
    by_cases h : 2 ∣ n
    · left
      have hodd : ¬ 2 ∣ n-1 := by omega
      have hc : Nat.Coprime 2 (n-1) := Nat.prime_two.coprime_iff_not_dvd.mpr hodd
      exact (hc.pow_left 13).dvd_of_dvd_mul_right hdiv
    · right
      have hc : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr h
      exact (hc.pow_left 13).dvd_of_dvd_mul_left hdiv
  have hn : good n = true := by
    rcases par with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hm : j-1 ∈ List.range 1220 := List.mem_range.mpr (by omega)
      have hh := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp cert _ hm)).1
      rwa [show 8192 * (j-1+1) = n by omega] at hh
    · have hm : j-1 ∈ List.range 1220 := List.mem_range.mpr (by omega)
      have hh := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp cert _ hm)).2
      rwa [show 8192 * (j-1+1)+1 = n by omega] at hh
  let q := n*(n-1) / Nat.gcd (n*(n-1)) (30030^48)
  have data : 1 < q ∧ q ∣ n*(n-1) ∧ q.Coprime 30030 := of_decide_eq_true hn
  let p := q.minFac
  have prime : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ q := Nat.minFac_dvd q
  have lower : 17 ≤ p := by
    by_contra! small
    have ht : ∀ i : Fin 17, i.val.Prime → i.val ∣ 30030 := by decide
    have hp := ht ⟨p, small⟩ prime
    exact prime.not_dvd_one (data.2.2.gcd_eq_one ▸ Nat.dvd_gcd hd hp)
  intro allPrimes
  have dvd : (17:ℕ).factorial ∣ n*(n-1) := (Nat.factorial_dvd_factorial lower).trans
    (allPrimes p prime (hd.trans data.2.1))
  have bound := Nat.le_of_dvd (by exact Nat.mul_pos (by omega) (by omega)) dvd
  have upper := Nat.mul_le_mul hi (show n-1 ≤ 10000000 by omega)
  norm_num [Nat.factorial] at bound
  omega

end HickersonRange

namespace OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1_H2_R1

/-- The largest factorial is at least three below the target. -/
def H1 : Prop := ∀ (n : ℕ) (l : List ℕ), (n,l) ∈ Erdos373.S → l.headI + 2 < n → n ≤ 16

/-- At gap two, any surviving n exceeds ten million and its consecutive product passes both sieves. -/
def H2 : Prop := ∀ (n : ℕ) (l : List ℕ), 10000000 < n → 8192 ∣ n*(n-1) →
  (∀ p : ℕ, p.Prime → p ∣ n*(n-1) → p.factorial ∣ n*(n-1)) →
  l.Pairwise (· ≥ ·) → (∀ a ∈ l, 1 < a) → (∀ a ∈ l, a ≤ n-2) →
  n*(n-1) ≠ (l.map Nat.factorial).prod

theorem main : H1 → H2 → OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1.H2 := by
  intro far near s hS
  obtain ⟨n,l⟩ := s
  change n ≤ 16
  have hgap := hS.2.2.1
  change l.headI < n-1 at hgap
  by_cases hfar : l.headI + 2 < n
  · exact far n l hS hfar
  by_contra! hlarge
  have he : l.headI + 2 = n := by omega
  cases l with
  | nil => simp at he; omega
  | cons a l =>
    change a + 2 = n at he
    subst n
    have hfac : (a+2).factorial = a.factorial * (l.map Nat.factorial).prod := hS.1
    have hp : (a+2)*(a+1) = (l.map Nat.factorial).prod := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos a)
      simpa [Nat.factorial_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfac
    have hd : a+2-1 = a+1 := by omega
    rw [← hd] at hp
    have hs : (a :: l).Pairwise (· ≥ ·) := hS.2.1
    have hmin : ∀ t ∈ l, 1 < t := fun t ht => hS.2.2.2 t (by simp [ht])
    have hup : ∀ t ∈ l, t ≤ a+2-2 := fun t ht => by simpa using (List.pairwise_cons.mp hs).1 t ht
    have hdvd := HickersonBudget.gapTwo_large_divisor (a+2) l (List.pairwise_cons.mp hs).2 hmin hp hlarge
    have sieve (p : ℕ) (hprime : p.Prime) (hdiv : p ∣ (a+2)*(a+2-1)) : p.factorial ∣ (a+2)*(a+2-1) := by
      rw [hp] at hdiv ⊢
      exact HickersonBudget.prime_factorial_dvd l p hprime hdiv
    have beyond : 10000000 < a+2 := by
      by_contra! hi
      exact HickersonRange.smooth_exclusion (a+2) hlarge hi hdvd sieve
    exact near _ l beyond hdvd sieve (List.pairwise_cons.mp hs).2 hmin hup hp

end OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1_H2_R1

