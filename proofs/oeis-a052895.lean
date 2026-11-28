import OMAStatements.S_oeis_a052895
import Mathlib

/-
A052895: the sum over j of S(n,j) j! Catalan(j) is eventually periodic modulo k with period
phi(k). Only the Stirling part matters; the weights can be arbitrary.

Method, for any S with the Stirling recurrence S(n+1, j+1) = (j+1) S(n, j+1) + S(n, j):
- surj: S(n,j) j! = sum over i <= j of (-1)^(j+i) C(j,i) i^n (the number of surjections), by
  induction on n, using i C(j+1,i) = (j+1) (C(j+1,i) - C(j,i)).
- pow_per: a^(n+d) = a^n modulo k whenever n >= k and phi(k) divides d, by strong induction on k
  (Euler when gcd(a,k) = 1, otherwise split off g = gcd(a,k) and use the case k/g).
- genper: for n >= k the terms with j >= k vanish modulo k because k divides j!, and each
  remaining term is an integer combination of powers i^n.
-/

namespace OMA.P052895

lemma pow_per : ∀ k : ℕ, 0 < k → ∀ a n d : ℕ, k ≤ n → k.totient ∣ d →
    a ^ (n + d) ≡ a ^ n [MOD k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk a n d hn hd
    rcases Nat.eq_or_lt_of_le (Nat.gcd_pos_of_pos_right a hk) with h | h
    · obtain ⟨t, rfl⟩ := hd
      have h1 : a ^ k.totient ≡ 1 [MOD k] := Nat.ModEq.pow_totient h.symm
      have h2 := (h1.pow t).mul_left (a ^ n)
      rw [one_pow, mul_one, ← pow_mul, ← pow_add] at h2
      exact h2
    · obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a k
      obtain ⟨k', hk'⟩ := Nat.gcd_dvd_right a k
      generalize Nat.gcd a k = g at h ha' hk'
      subst ha' hk'
      have hk'pos : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with h0 | h0
        · simp [h0] at hk
        · exact h0
      have h2k : 2 * k' ≤ g * k' := Nat.mul_le_mul_right k' h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hdvd : k'.totient ∣ d := (Nat.totient_dvd_of_dvd (Dvd.intro_left g rfl)).trans hd
      have h3 := ((ih k' (by omega) hk'pos (g * a') m d (by omega) hdvd).mul_left' g).mul_left a'
      have e1 : (g * a') ^ (m + 1 + d) = a' * (g * (g * a') ^ (m + d)) := by ring
      have e2 : (g * a') ^ (m + 1) = a' * (g * (g * a') ^ m) := by ring
      rw [e1, e2]
      exact h3

lemma chooseK (j i : ℕ) : (i : ℤ) * ((j + 1).choose i : ℤ) =
    (j + 1) * (((j + 1).choose i : ℤ) - (j.choose i : ℤ)) := by
  rcases i with _ | m
  · simp
  · have h1 := Nat.add_one_mul_choose_eq j m
    have h2 := Nat.choose_succ_succ j m
    zify at h1 h2
    push_cast
    linear_combination (-1 : ℤ) * h1 - ((j : ℤ) + 1) * h2

lemma surj (S : ℕ → ℕ → ℕ) (h00 : S 0 0 = 1) (hn0 : ∀ n, S (n + 1) 0 = 0)
    (h0j : ∀ j, S 0 (j + 1) = 0)
    (hrec : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j) :
    ∀ n j : ℕ, (S n j : ℤ) * (j.factorial : ℤ) =
      ∑ i ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro j
    have e : ∀ i : ℕ, (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ 0 =
        (-1) ^ j * ((-1) ^ i * (j.choose i : ℤ)) := fun i => by rw [pow_add]; ring
    simp only [e, ← Finset.mul_sum, Int.alternating_sum_range_choose]
    rcases j with _ | j
    · simp [h00]
    · simp [h0j]
  | succ n ih =>
    intro j
    rcases j with _ | j
    · simp [hn0]
    · have ih1 := ih (j + 1)
      have ih0 := ih j
      have ext : ∑ i ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n =
          ∑ i ∈ Finset.range (j + 1 + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
        rw [Finset.sum_range_succ _ (j + 1)]
        simp [Nat.choose_succ_self]
      rw [ext] at ih0
      have lhs : (S (n + 1) (j + 1) : ℤ) * ((j + 1).factorial : ℤ) =
          (j + 1) * ((S n (j + 1) : ℤ) * ((j + 1).factorial : ℤ)) +
            (j + 1) * ((S n j : ℤ) * (j.factorial : ℤ)) := by
        rw [hrec, Nat.factorial_succ]
        push_cast
        ring
      rw [lhs, ih1, ih0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have K := chooseK j i
      have s : (-1 : ℤ) ^ (j + i) = -(-1) ^ (j + 1 + i) := by
        rw [show j + 1 + i = j + i + 1 by ring, pow_succ]
        ring
      rw [s, pow_succ]
      linear_combination (-((-1 : ℤ) ^ (j + 1 + i)) * (i : ℤ) ^ n) * K

lemma sum_modEq {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (m : ℤ)
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD m]) : ∑ i ∈ s, f i ≡ ∑ i ∈ s, g i [ZMOD m] := by
  rw [Int.modEq_iff_dvd, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i hi => Int.modEq_iff_dvd.1 (h i hi)

lemma genper (S : ℕ → ℕ → ℕ) (h00 : S 0 0 = 1) (hn0 : ∀ n, S (n + 1) 0 = 0)
    (h0j : ∀ j, S 0 (j + 1) = 0)
    (hrec : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j)
    (g : ℕ → ℤ) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : k ≤ n) :
    (∑ j ∈ Finset.range (n + k.totient + 1),
        (S (n + k.totient) j : ℤ) * (j.factorial : ℤ) * g j) ≡
      ∑ j ∈ Finset.range (n + 1), (S n j : ℤ) * (j.factorial : ℤ) * g j [ZMOD (k : ℤ)] := by
  have trunc : ∀ m : ℕ, k ≤ m →
      (∑ j ∈ Finset.range (m + 1), (S m j : ℤ) * (j.factorial : ℤ) * g j) ≡
        ∑ j ∈ Finset.range k, (S m j : ℤ) * (j.factorial : ℤ) * g j [ZMOD (k : ℤ)] := by
    intro m hm
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ m + 1),
      Int.modEq_iff_dvd, sub_add_cancel_left]
    refine dvd_neg.2 (Finset.dvd_sum fun j hj => ?_)
    have hj' : k ≤ j := (Finset.mem_Ico.1 hj).1
    exact Dvd.dvd.mul_right
      (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hk hj')) _) _
  refine (trunc _ (by omega)).trans (Int.ModEq.trans ?_ (trunc n hn).symm)
  refine sum_modEq _ _ _ _ fun j _ => Int.ModEq.mul_right _ ?_
  rw [surj S h00 hn0 h0j hrec, surj S h00 hn0 h0j hrec]
  refine sum_modEq _ _ _ _ fun i _ => Int.ModEq.mul_left _ ?_
  have := pow_per k hk i n k.totient hn dvd_rfl
  exact_mod_cast (Int.natCast_modEq_iff.2 this)

lemma main' (S : ℕ → ℕ → ℕ) (h00 : S 0 0 = 1) (hn0 : ∀ n, S (n + 1) 0 = 0)
    (h0j : ∀ j, S 0 (j + 1) = 0)
    (hrec : ∀ n j, S (n + 1) (j + 1) = (j + 1) * S n (j + 1) + S n j) (g : ℕ → ℕ) :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ j ∈ Finset.range (n + Nat.totient k + 1), S (n + Nat.totient k) j * j.factorial * g j) ≡
        ∑ j ∈ Finset.range (n + 1), S n j * j.factorial * g j [MOD k] := by
  intro k hk
  refine ⟨k, fun n hn => ?_⟩
  have := genper S h00 hn0 h0j hrec (fun j => (g j : ℤ)) k hk n hn
  exact_mod_cast this

end OMA.P052895

theorem OMA.solution : type_of% @OMA.S_oeis_a052895.main :=
  OMA.P052895.main' OMA.S_oeis_a052895.stirling2 rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    catalan
