import OMAStatements.S_oeis_a392116

namespace OMA.R_oeis_a392116_R1

open OMA.S_oeis_a392116

/-- Consecutive prime pairs realizing positive gaps divisible by ten. -/
def H1 : Prop := ∀ k : ℕ, 0 < k → ∃ p : ℕ, p.Prime ∧ (p+10*k).Prime ∧
  ∀ q : ℕ, p < q → q < p+10*k → ¬ q.Prime

/-- Consecutive prime pairs realizing gaps four modulo ten, beyond five. -/
def H2 : Prop := ∀ k : ℕ, 0 < k → ∃ p : ℕ, 5 < p ∧ p.Prime ∧ (p+10*k+4).Prime ∧
  ∀ q : ℕ, p < q → q < p+10*k+4 → ¬ q.Prime

lemma consecutive {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hlt : p < r)
    (empty : ∀ q : ℕ, p < q → q < r → ¬ q.Prime) :
    ∃ n : ℕ, 1 ≤ n ∧ a n = r/5 - p/5 := by
  let i := Nat.count Nat.Prime p
  have h0 : Nat.nth Nat.Prime i = p := Nat.nth_count hp
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hl : p < Nat.nth Nat.Prime (i+1) := h0 ▸ hmono (Nat.lt_succ_self i)
  have hu : Nat.nth Nat.Prime (i+1) ≤ r := by
    rw [← Nat.nth_count hr]
    apply hmono.monotone
    have hi : i < Nat.count Nat.Prime r := by
      apply hmono.lt_iff_lt.mp
      rwa [h0,Nat.nth_count hr]
    omega
  have he : Nat.nth Nat.Prime (i+1) = r := by
    by_contra h
    exact empty _ hl (by omega) (Nat.prime_nth_prime _)
  exact ⟨i+1,by omega,by simp [a,he,h0]⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a392116.main := by
  intro evenGap oddGap m
  by_cases h0 : m = 0
  · subst m
    exact ⟨1,by decide,by norm_num [a,Nat.nth_prime_one_eq_three,Nat.nth_prime_zero_eq_two]⟩
  by_cases h1 : m = 1
  · subst m
    exact ⟨2,by decide,by norm_num [a,Nat.nth_prime_one_eq_three,Nat.nth_prime_two_eq_five]⟩
  let k := m/2
  have hk : 0 < k := by dsimp [k]; omega
  by_cases e : m%2 = 0
  · obtain ⟨p,hp,hr,empty⟩ := evenGap k hk
    obtain ⟨n,hn,ha⟩ := consecutive hp hr (by omega) empty
    exact ⟨n,hn,by dsimp [k] at ha; omega⟩
  · obtain ⟨p,hp5,hp,hr,empty⟩ := oddGap k hk
    obtain ⟨n,hn,ha⟩ := consecutive hp hr (by omega) empty
    have hres : p%5 ≠ 0 := by
      intro h
      have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp
        (Nat.dvd_of_mod_eq_zero h)
      omega
    exact ⟨n,hn,by dsimp [k] at ha; omega⟩

end OMA.R_oeis_a392116_R1
