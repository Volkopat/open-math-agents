import OMAStatements.S_oeis_a376182

/-! The even and odd entries each partition their parity class into consecutive row intervals. -/
-- Credit: @STARDUSTLC666

namespace TriangleParity

open OMA.S_oeis_a376182

-- Number of even columns in the first n rows.
private def boundary (n : ℕ) : ℤ := (↑(n/2) : ℤ) * ↑((n+1)/2)

private lemma advance (n : ℕ) :
    boundary (n+1) = boundary n + ((n+1)/2 : ℕ) := by
  unfold boundary
  rw [show (n+1+1)/2 = n/2+1 by omega]
  push_cast
  ring

private lemma nonneg (n : ℕ) : 0 ≤ boundary n := by
  unfold boundary
  positivity

private lemma monotone_boundary : Monotone boundary := by
  apply monotone_nat_of_le_succ
  intro n
  rw [advance]
  omega

private lemma lower (n : ℕ) : (n : ℤ) ≤ boundary (n+1) := by
  induction n with
  | zero => exact nonneg 1
  | succ n ih =>
    rw [advance (n+1)]
    omega

private lemma locate {t : ℤ} (ht : 0 < t) :
    ∃ n : ℕ, boundary n < t ∧ t ≤ boundary (n+1) := by
  have ex : ∃ n : ℕ, t ≤ boundary (n+1) := ⟨t.toNat, by have := lower t.toNat; omega⟩
  let n := Nat.find ex
  refine ⟨n, ?_, Nat.find_spec ex⟩
  rcases eq_or_ne n 0 with z | hz
  · simpa [z, boundary] using ht
  · have prev := Nat.find_min ex (m := n-1) (show n-1 < n by omega)
    simpa [show n-1+1 = n by omega] using lt_of_not_ge prev

private lemma unique_interval {n m : ℕ} {t : ℤ}
    (a : boundary n < t) (b : t ≤ boundary (n+1))
    (c : boundary m < t) (d : t ≤ boundary (m+1)) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · have := monotone_boundary (show n+1 ≤ m by omega)
    omega
  · exact h
  · have := monotone_boundary (show m+1 ≤ n by omega)
    omega

private lemma header (n : ℕ) :
    (2*(n : ℤ)^2 + 4*n + 1 - paritySign n)/4 = 2*boundary (n+1) := by
  obtain ⟨q, rfl | rfl⟩ : ∃ q, n = 2*q ∨ n = 2*q+1 := ⟨n/2, by omega⟩
  · unfold paritySign boundary
    rw [if_pos (show (2*q)%2 = 0 by omega),
      show (2*q+1)/2 = q by omega, show (2*q+1+1)/2 = q+1 by omega]
    push_cast
    ring_nf
    omega
  · unfold paritySign boundary
    rw [if_neg (show (2*q+1)%2 ≠ 0 by omega),
      show (2*q+1+1)/2 = q+1 by omega, show (2*q+1+1+1)/2 = q+1 by omega]
    push_cast
    ring_nf
    omega

-- Row n+1 starts its even entries just above 2*boundary n.
-- Its odd entries descend from just below 2*boundary (n+2).
private def value (n k : ℕ) : ℤ :=
  if k%2 = 0 then 2*boundary n + k else 2*boundary (n+1+1) - k

private lemma entry_at (n k : ℕ) (lo : 1 ≤ k) (hi : k ≤ n+1) :
    entry ⟨(n+1,k), lo, hi⟩ = value n k := by
  change (2*((n+1 : ℕ) : ℤ)^2 + 4*((n+1 : ℕ) : ℤ) + 1 - paritySign (n+1))/4 -
    (1+paritySign k)*(((n+1 : ℕ) : ℤ)-k)-k = _
  rw [header]
  have h := advance n
  have h' := advance (n+1)
  by_cases even : k%2 = 0 <;> simp [value, paritySign, even] <;> omega

private lemma cell_data (p : Cell) :
    ∃ n k : ℕ, ∃ lo : 1 ≤ k, ∃ hi : k ≤ n+1, p = ⟨(n+1,k), lo, hi⟩ := by
  obtain ⟨⟨n,k⟩,lo,hi⟩ := p
  cases n with
  | zero => omega
  | succ n => exact ⟨n,k,lo,hi,rfl⟩

private lemma bounds {n k : ℕ} {u : ℤ} (lo : 1 ≤ k) (hi : k ≤ n+1) (hu : value n k = u) :
    if u%2 = 0 then boundary n < u/2 ∧ u/2 ≤ boundary (n+1) ∧ u = 2*boundary n + k
    else boundary (n+1) < (u+1)/2 ∧ (u+1)/2 ≤ boundary (n+1+1) ∧ u = 2*boundary (n+1+1)-k := by
  have h := advance n
  have h' := advance (n+1)
  unfold value at hu
  split at hu <;> split <;> omega

private lemma injective_entry : Function.Injective entry := by
  intro p q eq
  obtain ⟨n,k,lo,hi,rfl⟩ := cell_data p
  obtain ⟨m,j,lo',hi',rfl⟩ := cell_data q
  rw [entry_at n k lo hi, entry_at m j lo' hi'] at eq
  have a := bounds lo hi (rfl : value n k = value n k)
  have b := bounds lo' hi' eq.symm
  by_cases parity : value n k % 2 = 0
  · rw [if_pos parity] at a b
    have rows := unique_interval a.1 a.2.1 b.1 b.2.1
    subst m
    have cols : k = j := by omega
    subst j
    rfl
  · rw [if_neg parity] at a b
    have rows := unique_interval a.1 a.2.1 b.1 b.2.1
    have same : n = m := by omega
    subst m
    have cols : k = j := by omega
    subst j
    rfl

private lemma occurs (u : ℤ) (hu : 0 < u) : ∃ p : Cell, entry p = u := by
  by_cases parity : u%2 = 0
  · obtain ⟨n, left, right⟩ := locate (t := u/2) (by omega)
    let k := (u-2*boundary n).toNat
    have ek : (k : ℤ) = u-2*boundary n := by dsimp [k]; omega
    have h := advance n
    have lo : 1 ≤ k := by omega
    have hi : k ≤ n+1 := by omega
    refine ⟨⟨(n+1,k), lo, hi⟩, ?_⟩
    rw [entry_at n k lo hi, value, if_pos (show k%2 = 0 by omega)]
    omega
  · obtain ⟨m, left, right⟩ := locate (t := (u+1)/2) (by omega)
    cases m with
    | zero => norm_num [boundary] at right; omega
    | succ n =>
      let k := (2*boundary (n+1+1)-u).toNat
      have ek : (k : ℤ) = 2*boundary (n+1+1)-u := by dsimp [k]; omega
      have h := advance (n+1)
      have lo : 1 ≤ k := by omega
      have hi : k ≤ n+1 := by omega
      refine ⟨⟨(n+1,k), lo, hi⟩, ?_⟩
      rw [entry_at n k lo hi, value, if_neg (show k%2 ≠ 0 by omega)]
      omega

end TriangleParity

open TriangleParity OMA.S_oeis_a376182

theorem OMA.solution : type_of% @OMA.S_oeis_a376182.main := by
  constructor
  · intro p
    obtain ⟨n,k,lo,hi,rfl⟩ := cell_data p
    rw [entry_at n k lo hi]
    have h := bounds lo hi (rfl : value n k = value n k)
    have h0 := nonneg n
    have h1 := nonneg (n+1)
    split at h <;> omega
  · intro u hu
    obtain ⟨p,hp⟩ := occurs u hu
    exact ⟨p, hp, fun q hq => injective_entry (hq.trans hp.symm)⟩
