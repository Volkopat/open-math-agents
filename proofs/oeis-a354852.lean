import OMAStatements.S_oeis_a354852
import Mathlib

/-!
Proof of the A354852 claim a(p) = a(p-1)+1 for primes p.
Strings are little-endian, so the least significant (last written) digit is the head of the list.
The strings for p are the string 10 (head 0) together with the images of the strings for p - 1 under the
map that adds one to the head digit; no carry can occur, since a carry would write p as a product of
two numbers that are both at least 2.
-/

namespace OMA.A354852Proof

open OMA.S_oeis_a354852

theorem rep_nil (n : ℕ) : ¬ Rep [] n := fun h => h

theorem rep_single (d n : ℕ) : Rep [d] n ↔ d ≠ 0 ∧ d = n := Iff.rfl

theorem rep_cons2 (d e : ℕ) (ds : List ℕ) (n : ℕ) :
    Rep (d :: e :: ds) n ↔ ∃ b m : ℕ, 2 ≤ b ∧ d < b ∧ Rep (e :: ds) m ∧ n = d + b * m := Iff.rfl

/-- Every represented number is at least 1. -/
theorem rep_pos : ∀ (l : List ℕ) (n : ℕ), Rep l n → 1 ≤ n
  | [], n, h => absurd h (rep_nil n)
  | [d], n, h => by
      rw [rep_single] at h
      omega
  | d :: e :: ds, n, h => by
      rw [rep_cons2] at h
      obtain ⟨b, m, hb, _, hr, hn⟩ := h
      have hm := rep_pos (e :: ds) m hr
      have hbm := Nat.mul_le_mul hb hm
      omega

/-- The only string representing 1 is the one-digit string 1. -/
theorem rep_one (l : List ℕ) (h : Rep l 1) : l = [1] := by
  match l, h with
  | [], h => exact absurd h (rep_nil 1)
  | [d], h =>
      rw [rep_single] at h
      rw [h.2]
  | d :: e :: ds, h =>
      rw [rep_cons2] at h
      obtain ⟨b, m, hb, _, hr, hn⟩ := h
      have hm := rep_pos (e :: ds) m hr
      have hbm := Nat.mul_le_mul hb hm
      exfalso
      omega

/-- Finiteness, by strong induction: a string for `n` is `[n]` or a digit `d ≤ n` in front of a
string for some `m < n`. -/
theorem rep_finite_lt : ∀ k n : ℕ, n < k → {l : List ℕ | Rep l n}.Finite := by
  intro k
  induction k with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ k ih =>
    intro n hn
    have hsub : {l : List ℕ | Rep l n} ⊆
        {[n]} ∪ ⋃ m ∈ {i : ℕ | i < n}, ⋃ d ∈ {i : ℕ | i ≤ n},
          (List.cons d) '' {l : List ℕ | Rep l m} := by
      intro l hl
      change Rep l n at hl
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image, exists_prop]
      match l, hl with
      | [], h => exact absurd h (rep_nil n)
      | [d], h =>
          rw [rep_single] at h
          exact Or.inl (by rw [h.2])
      | d :: e :: ds, h =>
          rw [rep_cons2] at h
          obtain ⟨b, m, hb, _, hr, hn'⟩ := h
          have hm := rep_pos (e :: ds) m hr
          have hbm2 : 2 * m ≤ b * m := Nat.mul_le_mul hb (le_refl m)
          exact Or.inr ⟨m, (show m < n by omega), d, (show d ≤ n by omega), e :: ds, hr, rfl⟩
    refine Set.Finite.subset ?_ hsub
    refine (Set.finite_singleton _).union ?_
    refine (Set.finite_lt_nat n).biUnion fun m hm => ?_
    refine (Set.finite_le_nat n).biUnion fun d _ => ?_
    change m < n at hm
    exact (ih m (by omega)).image _

theorem rep_finite (n : ℕ) : {l : List ℕ | Rep l n}.Finite :=
  rep_finite_lt (n + 1) n (Nat.lt_succ_self n)

/-- Add one to the least significant digit (the head of the list). -/
def inc : List ℕ → List ℕ
  | [] => []
  | d :: ds => (d + 1) :: ds

theorem inc_injective : Function.Injective inc := by
  intro x y h
  match x, y, h with
  | [], [], _ => rfl
  | [], _ :: _, h => simp [inc] at h
  | _ :: _, [], h => simp [inc] at h
  | u :: us, v :: vs, h =>
      simp only [inc, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [show u = v by omega, h2]

/-- For a prime `p`, the strings for `p` are the string 10 and the strings for `p - 1` with the
least significant digit increased by one. -/
theorem rep_prime_eq (p : ℕ) (hp : p.Prime) :
    {l : List ℕ | Rep l p} = insert [0, 1] (inc '' {l : List ℕ | Rep l (p - 1)}) := by
  have hp2 := hp.two_le
  ext l
  simp only [Set.mem_insert_iff, Set.mem_image]
  change Rep l p ↔ l = [0, 1] ∨ ∃ x, Rep x (p - 1) ∧ inc x = l
  constructor
  · intro hl
    match l, hl with
    | [], h => exact absurd h (rep_nil p)
    | [d], h =>
        rw [rep_single] at h
        refine Or.inr ⟨[p - 1], ?_, ?_⟩
        · rw [rep_single]
          omega
        · show [p - 1 + 1] = [d]
          rw [show p - 1 + 1 = d by omega]
    | d :: e :: ds, h =>
        rw [rep_cons2] at h
        obtain ⟨b, m, hb, hd, hr, hn⟩ := h
        have hm := rep_pos (e :: ds) m hr
        rcases Nat.eq_zero_or_pos d with hd0 | hd0
        · subst hd0
          have hdvd : b ∣ p := ⟨m, by omega⟩
          rcases hp.eq_one_or_self_of_dvd b hdvd with hb1 | hbp
          · exfalso
            omega
          · rw [hbp] at hn
            have h1 : p * m = p * 1 := by omega
            have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_left (by omega) h1
            rw [hm1] at hr
            refine Or.inl ?_
            rw [rep_one (e :: ds) hr]
        · refine Or.inr ⟨(d - 1) :: e :: ds, ?_, ?_⟩
          · rw [rep_cons2]
            exact ⟨b, m, hb, by omega, hr, by omega⟩
          · show (d - 1 + 1) :: e :: ds = d :: e :: ds
            rw [show d - 1 + 1 = d by omega]
  · rintro (rfl | ⟨l', hl', rfl⟩)
    · rw [rep_cons2]
      refine ⟨p, 1, hp2, by omega, ?_, by omega⟩
      rw [rep_single]
      exact ⟨by omega, rfl⟩
    · match l', hl' with
      | [], h => exact absurd h (rep_nil _)
      | [d], h =>
          rw [rep_single] at h
          obtain ⟨h1, h2⟩ := h
          show Rep [d + 1] p
          rw [rep_single]
          constructor <;> omega
      | d :: e :: ds, h =>
          rw [rep_cons2] at h
          obtain ⟨b, m, hb, hd, hr, hn⟩ := h
          have hm := rep_pos (e :: ds) m hr
          show Rep ((d + 1) :: e :: ds) p
          rw [rep_cons2]
          refine ⟨b, m, hb, ?_, hr, by omega⟩
          by_contra hcon
          have hdb : d + 1 = b := by omega
          have hpb : p = b * (m + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          have hdvd : b ∣ p := ⟨m + 1, hpb⟩
          rcases hp.eq_one_or_self_of_dvd b hdvd with hb1 | hbp
          · omega
          · rw [hbp] at hpb
            have h3 : p * (m + 1) = p * 1 := by omega
            have h4 := Nat.eq_of_mul_eq_mul_left (by omega) h3
            omega

theorem solution_aux :
    (∀ n : ℕ, {l : List ℕ | Rep l n}.Finite) ∧ ∀ p : ℕ, p.Prime → a p = a (p - 1) + 1 := by
  refine ⟨rep_finite, fun p hp => ?_⟩
  have hnot : [0, 1] ∉ inc '' {l : List ℕ | Rep l (p - 1)} := by
    rintro ⟨x, _, hx⟩
    match x, hx with
    | [], h => simp [inc] at h
    | d :: ds, h =>
        change (d + 1) :: ds = [0, 1] at h
        injection h with h1 h2
        omega
  unfold a
  rw [rep_prime_eq p hp, Set.ncard_insert_of_notMem hnot ((rep_finite _).image _),
    Set.ncard_image_of_injective _ inc_injective]

end OMA.A354852Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a354852.main := by
  exact OMA.A354852Proof.solution_aux
