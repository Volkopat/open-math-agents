import OMAStatements.S_oeis_a028231

namespace Extra028231

/-- Every nonminimal positive solution has a strictly smaller predecessor under
multiplication by the inverse Pell unit. The coordinate inequalities ensure
that the inverse formulas have exactly their intended values in ℕ. -/
theorem descent {k t : ℕ} (h : k ^ 2 + k + 1 = 3 * t ^ 2) :
    (k = 1 ∧ t = 1) ∨ ∃ j u : ℕ, j < k ∧ j ^ 2 + j + 1 = 3 * u ^ 2 ∧
      k = 7 * j + 3 + 12 * u ∧ t = 4 * j + 2 + 7 * u := by
  by_cases hk : 11 ≤ k
  · right
    have hk2 := Nat.mul_le_mul_left k hk
    have hfirst : 12 * t ≤ 7 * k + 3 := by
      by_contra! hbad
      nlinarith [Nat.mul_self_le_mul_self hbad.le]
    have hsecond : 4 * k + 2 ≤ 7 * t := by
      by_contra! hbad
      nlinarith [Nat.mul_self_le_mul_self hbad.le]
    have hdrop : 6 * k + 3 < 12 * t := by
      by_contra! hbad
      nlinarith [Nat.mul_self_le_mul_self hbad]
    let j := 7 * k + 3 - 12 * t
    let u := 7 * t - (4 * k + 2)
    have hj : j + 12 * t = 7 * k + 3 := Nat.sub_add_cancel hfirst
    have hu : u + (4 * k + 2) = 7 * t := Nat.sub_add_cancel hsecond
    refine ⟨j, u, by omega, ?_, by omega, by omega⟩
    have hz : (k : ℤ) ^ 2 + k + 1 = 3 * (t : ℤ) ^ 2 := by exact_mod_cast h
    have jz : (j : ℤ) = 7 * (k : ℤ) + 3 - 12 * (t : ℤ) := by omega
    have uz : (u : ℤ) = 7 * (t : ℤ) - (4 * (k : ℤ) + 2) := by omega
    have pred : (j : ℤ) ^ 2 + j + 1 = 3 * (u : ℤ) ^ 2 := by
      rw [jz, uz]
      nlinarith only [hz]
    exact_mod_cast pred
  · left
    have hkle : k ≤ 10 := by omega
    have htle : t ≤ 6 := by
      by_contra! hbad
      have h7 : 7 ≤ t := hbad
      nlinarith [Nat.mul_self_le_mul_self hkle, Nat.mul_self_le_mul_self h7]
    interval_cases k <;> interval_cases t <;> norm_num at *

end Extra028231

namespace Extra028231

/-- A strictly increasing enumeration agrees with the natural enumeration of its range. -/
theorem nth_enum {P : ℕ → Prop} (f : ℕ → ℕ) (hf : StrictMono f)
    (hterms : ∀ k, P k ↔ ∃ n, f n = k) (n : ℕ) : Nat.nth P n = f n := by
  have hr : Set.ofPred P = Set.range f := by
    ext k
    exact hterms k
  have hi : (Set.ofPred P).Infinite := by
    rw [hr]
    exact Set.infinite_range_of_injective hf.injective
  have hall (i : ℕ) : ∀ h : (Set.ofPred P).Finite, i < h.toFinset.card :=
    fun h => (hi h).elim
  symm
  refine Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := P) f ?_ ?_ (hf.strictMonoOn _) (hall n)
  · intro y hy
    obtain ⟨i,hi'⟩ := (hterms y).mp hy
    exact ⟨i,hall i,hi'⟩
  · intro i _
    exact (hterms (f i)).mpr ⟨i,rfl⟩

end Extra028231

namespace Extra028231

def orbit : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => (7 * (orbit n).1 + 3 + 12 * (orbit n).2,
      4 * (orbit n).1 + 2 + 7 * (orbit n).2)

theorem orbit_equation (n : ℕ) :
    (orbit n).1 ^ 2 + (orbit n).1 + 1 = 3 * (orbit n).2 ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [orbit]
    nlinarith only [ih]

theorem orbit_increasing : StrictMono (fun n => (orbit n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change (orbit n).1 < 7 * (orbit n).1 + 3 + 12 * (orbit n).2
  omega

theorem orbit_covers (k : ℕ) : ∀ t : ℕ, k ^ 2 + k + 1 = 3 * t ^ 2 →
    ∃ n : ℕ, orbit n = (k, t) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t heq
    rcases descent heq with ⟨rfl, rfl⟩ | ⟨j, u, hj, hju, hk, ht⟩
    · exact ⟨0, rfl⟩
    · obtain ⟨m, hm⟩ := ih j hj u hju
      exact ⟨m + 1, by simp only [orbit, hm, hk, ht]⟩

open OMA.S_oeis_a028231

theorem term_equation (k : ℕ) : IsTerm k ↔ ∃ t : ℕ, k ^ 2 + k + 1 = 3 * t ^ 2 := by
  constructor
  · rintro ⟨hd, t, ht⟩
    refine ⟨t, ?_⟩
    calc
      k ^ 2 + k + 1 = ((k ^ 2 + k + 1) / 3) * 3 := (Nat.div_mul_cancel hd).symm
      _ = 3 * t ^ 2 := by rw [ht]; ring
  · rintro ⟨t, ht⟩
    unfold IsTerm
    rw [ht]
    exact ⟨dvd_mul_right _ _, t, by simp [pow_two]⟩

theorem term_orbit (k : ℕ) : IsTerm k ↔ ∃ n : ℕ, (orbit n).1 = k := by
  rw [term_equation]
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨n, hn⟩ := orbit_covers k t h
    exact ⟨n, by rw [hn]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(orbit n).2, orbit_equation n⟩

theorem sequence_eq (n : ℕ) : a n = (orbit n).1 :=
  nth_enum (fun m => (orbit m).1) orbit_increasing term_orbit n

end Extra028231

theorem OMA.solution : type_of% @OMA.S_oeis_a028231.main := by
  intro n
  simp only [Extra028231.sequence_eq, Extra028231.orbit, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  ring
