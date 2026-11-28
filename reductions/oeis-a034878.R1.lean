import OMAStatements.S_oeis_a034878
import Mathlib

/-!
# OEIS A034878: reduce the conjecture to composite consecutive inputs

Appending `(k - 1)!` proves the forward inclusion of Jordan–Pólya numbers, as observed
by Murthy and Sondow (https://oeis.org/A034878/internal). The examples at 9 and 10
also come from that entry.

If a prime divides a product of factorials, it must divide one of the factors, whose
index is therefore at least that prime. This eliminates prime inputs and proves the
converse when the predecessor is prime, by cancellation of the forced factor.
For odd inputs with a prime two below, the same cancellation leaves two
consecutive factors. A bound on their 2-adic valuation settles one subcase.
-/

namespace OMA.R_oeis_a034878_R1

open OMA.S_oeis_a034878

private theorem jp_in_sequence {k : ℕ} (hk : 1 ≤ k) (hk₂ : k ≠ 2)
    (hjp : IsJordanPolya k) : InA034878 k := by
  by_cases hk₁ : k = 1
  · subst k
    exact ⟨[], by simp, by decide⟩
  have hk₃ : 3 ≤ k := by omega
  obtain ⟨l, hl⟩ := hjp
  refine ⟨(k - 1) :: l, ?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · have hd : m.factorial ∣ k := by
        rw [← hl]
        exact List.dvd_prod (List.mem_map.mpr ⟨m, hm, rfl⟩)
      have hle := Nat.le_of_dvd (by omega : 0 < k) hd
      by_contra! hkm
      exact (not_lt_of_ge (Nat.le_trans (Nat.factorial_le hkm) hle))
        (Nat.lt_factorial_self hk₃)
  · simp only [List.map_cons, List.prod_cons, hl]
    rw [Nat.mul_comm, Nat.mul_factorial_pred (by omega : k ≠ 0)]

private theorem split_at_prime {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hd : p ∣ (l.map Nat.factorial).prod) :
    ∃ m ∈ l, p ≤ m ∧ ∃ rest : List ℕ,
      (l.map Nat.factorial).prod = m.factorial * (rest.map Nat.factorial).prod := by
  induction l with
  | nil => exact (hp.not_dvd_one (by simpa using hd)).elim
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons] at hd
    rcases hp.dvd_mul.mp hd with ha | ht
    · exact ⟨a, by simp, hp.dvd_factorial.mp ha, l, rfl⟩
    · obtain ⟨m, hm, hpm, rest, hrest⟩ := ih ht
      refine ⟨m, List.mem_cons_of_mem _ hm, hpm, a :: rest, ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [hrest, Nat.mul_left_comm a.factorial]

private theorem prime_excluded {p : ℕ} (hp : p.Prime) : ¬ InA034878 p := by
  rintro ⟨l, hl, hprod⟩
  have hd : p ∣ (l.map Nat.factorial).prod := by
    rw [hprod]
    exact Nat.dvd_factorial hp.pos le_rfl
  obtain ⟨m, hm, hpm, _⟩ := split_at_prime hp l hd
  exact (not_lt_of_ge hpm) (hl m hm)

private theorem jp_of_prime_pred {p : ℕ} (hp : p.Prime)
    (hseq : InA034878 (p + 1)) : IsJordanPolya (p + 1) := by
  obtain ⟨l, hl, hprod⟩ := hseq
  have hd : p ∣ (l.map Nat.factorial).prod := by
    rw [hprod]
    exact Nat.dvd_factorial hp.pos (by omega)
  obtain ⟨m, hm, hpm, rest, hrest⟩ := split_at_prime hp l hd
  have hlt := hl m hm
  have heq : m = p := by omega
  subst m
  rw [hprod, Nat.factorial_succ, Nat.mul_comm (p + 1)] at hrest
  exact ⟨rest, (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos p) hrest).symm⟩

private theorem jp_eq_one_of_odd {k : ℕ} (hjp : IsJordanPolya k) (hodd : ¬ 2 ∣ k) :
    k = 1 := by
  obtain ⟨l, rfl⟩ := hjp
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons] at hodd ⊢
    have ha : a.factorial = 1 := by
      apply Nat.factorial_eq_one.mpr
      by_contra! h
      exact hodd (dvd_mul_of_dvd_left (Nat.dvd_factorial (by decide) h) _)
    simpa [ha] using ih (by simpa [ha] using hodd)

private theorem jp_mul_pred_of_prime_pred_two {k : ℕ} (hk : 3 ≤ k)
    (hp : (k - 2).Prime) (hodd : ¬ 2 ∣ k) (hseq : InA034878 k) :
    IsJordanPolya (k * (k - 1)) := by
  obtain ⟨l, hl, hprod⟩ := hseq
  have hd : k - 2 ∣ (l.map Nat.factorial).prod := by
    rw [hprod]
    exact Nat.dvd_factorial hp.pos (by omega)
  obtain ⟨m, hm, hpm, rest, hrest⟩ := split_at_prime hp l hd
  have hmk := hl m hm
  have hc : m = k - 1 ∨ m = k - 2 := by omega
  rcases hc with rfl | rfl
  · have hfact : k.factorial = (k - 1).factorial * k := by
      rw [Nat.mul_comm, Nat.mul_factorial_pred (by omega)]
    rw [hprod, hfact] at hrest
    have hjp : IsJordanPolya k :=
      ⟨rest, (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) hrest).symm⟩
    exact (by omega : k ≠ 1) (jp_eq_one_of_odd hjp hodd) |>.elim
  · have hk1 : k - 1 ≠ 0 := by omega
    have hpred : k - 1 - 1 = k - 2 := by omega
    have hfact : k.factorial = (k - 2).factorial * (k * (k - 1)) := by
      calc
        k.factorial = k * (k - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
        _ = k * ((k - 1) * (k - 2).factorial) := by
          rw [← hpred, Nat.mul_factorial_pred hk1]
        _ = _ := by ac_rfl
    rw [hprod, hfact] at hrest
    exact ⟨rest, (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) hrest).symm⟩

private theorem factorial_product_pos (l : List ℕ) :
    0 < (l.map Nat.factorial).prod := by
  induction l with
  | nil => decide
  | cons a l ih => exact Nat.mul_pos (Nat.factorial_pos a) ih

/-- A factorial product with 2-adic valuation at most three is bounded by
the corresponding power of six. Only the factors with index at most five
can occur in such a product. -/
private theorem factorial_product_le_of_not_sixteen_dvd (l : List ℕ)
    (h : ¬ 16 ∣ (l.map Nat.factorial).prod) :
    (l.map Nat.factorial).prod ≤ 6 ^ ((l.map Nat.factorial).prod.factorization 2) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons] at h ⊢
    have ht : ¬ 16 ∣ (l.map Nat.factorial).prod := fun ht =>
      h (dvd_mul_of_dvd_right ht _)
    have ha : a < 6 := by
      by_contra! hag
      have hdiv : 16 ∣ a.factorial :=
        (show 16 ∣ (6 : ℕ).factorial by decide).trans (Nat.factorial_dvd_factorial hag)
      exact h (dvd_mul_of_dvd_left hdiv _)
    have hb : a.factorial ≤ 6 ^ (a.factorial.factorization 2) := by
      have hsmall (m e : ℕ) (hd : 2 ^ e ∣ m.factorial)
          (hle : m.factorial ≤ 6 ^ e) : m.factorial ≤ 6 ^ (m.factorial.factorization 2) :=
        hle.trans (Nat.pow_le_pow_right (by decide)
          ((Nat.prime_two.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp hd))
      interval_cases a
      · exact hsmall 0 0 (by decide) (by decide)
      · exact hsmall 1 0 (by decide) (by decide)
      · exact hsmall 2 1 (by decide) (by decide)
      · exact hsmall 3 1 (by decide) (by decide)
      · exact hsmall 4 3 (by decide) (by decide)
      · exact hsmall 5 3 (by decide) (by decide)
    rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (factorial_product_pos l).ne',
      Finsupp.add_apply, pow_add]
    exact Nat.mul_le_mul hb (ih ht)

/-- Nine is the only odd composite term of A034878 with a prime two below it
and with residue different from one modulo sixteen. -/
theorem odd_prime_two_below {k : ℕ} (hk : 3 ≤ k) (hnp : ¬ k.Prime)
    (hp : (k - 2).Prime) (hodd : ¬ 2 ∣ k) (hmod : k % 16 ≠ 1)
    (hseq : InA034878 k) : k = 9 := by
  obtain ⟨l, hl⟩ := jp_mul_pred_of_prime_pred_two hk hp hodd hseq
  have hcop : Nat.Coprime 16 k := by
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left 4
  have h16 : ¬ 16 ∣ k * (k - 1) := by
    intro hdiv
    have hp16 : 16 ∣ k - 1 := hcop.dvd_of_dvd_mul_left hdiv
    omega
  have hpow : k * (k - 1) ≤ 6 ^ ((k * (k - 1)).factorization 2) := by
    have hcert := factorial_product_le_of_not_sixteen_dvd l (by rwa [hl])
    simpa only [hl] using hcert
  have hv : (k * (k - 1)).factorization 2 ≤ 3 := by
    by_contra! hv
    exact h16 ((Nat.pow_dvd_pow 2 (show 4 ≤ _ from hv)).trans (Nat.ordProj_dvd _ 2))
  have hbound : k * (k - 1) ≤ 216 :=
    hpow.trans (Nat.pow_le_pow_right (by decide) hv)
  have hk15 : k ≤ 15 := by
    by_contra! hkbig
    have hh := Nat.mul_le_mul (show 16 ≤ k by omega) (show 15 ≤ k - 1 by omega)
    omega
  have hc : k = 9 ∨ k = 15 := by
    interval_cases k <;> first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact (hnp (by decide)).elim
      | exact (hodd (by decide)).elim
  rcases hc with rfl | rfl
  · rfl
  · have hz : ((15 * (15 - 1) : ℕ).factorization 2) ≤ 1 := by
      by_contra! hz
      exact (by decide : ¬ 4 ∣ (15 * (15 - 1) : ℕ))
        ((Nat.pow_dvd_pow 2 (show 2 ≤ _ from hz)).trans (Nat.ordProj_dvd _ 2))
    have hle := hpow.trans (Nat.pow_le_pow_right (by decide : 0 < (6 : ℕ)) hz)
    norm_num at hle

/-- The remaining converse for even inputs. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ¬ k.Prime → ¬ (k - 1).Prime → 2 ∣ k →
    InA034878 k → IsJordanPolya k ∨ k = 10

/-- Beyond one, the remaining odd case is to show that nine is the only term. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ¬ k.Prime → ¬ (k - 1).Prime → ¬ 2 ∣ k →
    (¬ (k - 2).Prime ∨ k % 16 = 1) → InA034878 k → k = 9

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a034878.main := by
  intro heven hodd k hk
  constructor
  · intro hseq
    by_cases hk₁ : k = 1
    · subst k
      exact Or.inl ⟨⟨[], by decide⟩, by decide⟩
    have hnp : ¬ k.Prime := fun hp => prime_excluded hp hseq
    have hk₂ : k ≠ 2 := by
      rintro rfl
      exact hnp (by decide)
    have hk₃ : 3 ≤ k := by omega
    have jp_when_prev_prime (hprev : (k - 1).Prime) : IsJordanPolya k := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact jp_of_prime_pred (by simpa using hprev) hseq
    by_cases hkEven : 2 ∣ k
    · by_cases hprev : (k - 1).Prime
      · exact Or.inl ⟨jp_when_prev_prime hprev, hk₂⟩
      · rcases heven k hk₃ hnp hprev hkEven hseq with hjp | hten
        · exact Or.inl ⟨hjp, hk₂⟩
        · exact Or.inr (Or.inr hten)
    · have hprev : ¬ (k - 1).Prime := fun hp =>
        hk₁ (jp_eq_one_of_odd (jp_when_prev_prime hp) hkEven)
      by_cases hcase : ¬ (k - 2).Prime ∨ k % 16 = 1
      · exact Or.inr (Or.inl (hodd k hk₃ hnp hprev hkEven hcase hseq))
      · have hp : (k - 2).Prime := by
          by_contra hn
          exact hcase (Or.inl hn)
        have hmod : k % 16 ≠ 1 := fun h => hcase (Or.inr h)
        exact Or.inr (Or.inl (odd_prime_two_below hk₃ hnp hp hkEven hmod hseq))
  · rintro (⟨hjp, hk₂⟩ | rfl | rfl)
    · exact jp_in_sequence hk hk₂ hjp
    · exact ⟨[7, 3, 3, 2], by decide, by decide⟩
    · exact ⟨[7, 6], by decide, by decide⟩

end OMA.R_oeis_a034878_R1
