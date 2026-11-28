import FormalConjectures.Wikipedia.IdonealCompleteness

-- Credit: @duartec05
namespace OMA.R_Idoneal_idoneal_numbers_completeness_R2

/-- Classify the idoneal numbers with no prime square divisor. -/
def H1 : Prop :=
  ∀ n : ℕ, (∀ p : ℕ, p.Prime → ¬ p ^ 2 ∣ n) →
    Idoneal.IsIdoneal n → n ∈ Idoneal.knownIdonealNumbers

/-- For each of Euler's 65 bases, exclude its unlisted prime-square extensions
by exhibiting a representation. -/
def H2 : Prop :=
  ∀ m ∈ Idoneal.knownIdonealNumbers, ∀ p : ℕ, p.Prime →
    p ^ 2 * m ∉ Idoneal.knownIdonealNumbers →
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * m = a * b + b * c + a * c

lemma idoneal_of_square_mul {p m : ℕ} (hp : 0 < p)
    (h : Idoneal.IsIdoneal (p ^ 2 * m)) : Idoneal.IsIdoneal m := by
  rcases h with ⟨hpos, hnone⟩
  constructor
  · by_contra! hm
    have hm0 : m = 0 := by omega
    simp [hm0] at hpos
  · rintro ⟨a, b, c, ha, hab, hbc, hm⟩
    apply hnone
    refine ⟨p * a, p * b, p * c, Nat.mul_pos hp ha,
      Nat.mul_lt_mul_of_pos_left hab hp, Nat.mul_lt_mul_of_pos_left hbc hp, ?_⟩
    rw [hm]
    ring

theorem main : H1 → H2 → type_of% @Idoneal.idoneal_numbers_completeness := by
  intro hbase hext n
  refine Nat.strong_induction_on n ?_
  intro k ih hk
  by_cases hfactor : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ k
  · obtain ⟨p, hp, m, rfl⟩ := hfactor
    have hmid : Idoneal.IsIdoneal m := idoneal_of_square_mul hp.pos hk
    have hp2 : 1 < p ^ 2 := by
      have h := Nat.mul_le_mul hp.two_le hp.two_le
      rw [pow_two]
      omega
    have hlt : m < p ^ 2 * m := by
      simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right hp2 hmid.1
    have hmem := ih m hlt hmid
    by_contra hmiss
    exact hk.2 (hext m hmem p hp hmiss)
  · apply hbase k ?_ hk
    intro p hp hd
    exact hfactor ⟨p, hp, hd⟩

end OMA.R_Idoneal_idoneal_numbers_completeness_R2
