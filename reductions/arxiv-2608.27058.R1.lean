import OMAStatements.S_arxiv_2608_27058

-- Credit: @ryansolves
namespace OMA.R_arxiv_2608_27058_R1
open OMA.S_arxiv_2608_27058

/-- The necessary divisibility from the threshold criterion in Section 6. -/
def H1 : Prop := ∀ p r t : ℕ, p.Prime → p ≠ 2 → t < r →
  preperiod (p^r) ≤ t → p^(r-t) ∣ zigzag t

/-- Published period and preperiod bounds, needed only at p and p cubed. -/
def H2 : Prop := ∀ p k : ℕ, p.Prime → p ≠ 2 → (k = 1 ∨ k = 3) →
  ∀ n : ℕ, k ≤ n →
    zigzag (n + p^(k-1)*Nat.lcm (p-1) 4) ≡ zigzag n [MOD p^k]

/-- Only lifts of consecutive zero triples in the first mod-p period need testing.
Each surviving start is checked in a single finite window modulo p cubed. -/
def H3 : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 →
  let D := Nat.lcm (p-1) 4
  ∀ a : ℕ, 1 ≤ a → a ≤ D →
    p ∣ zigzag a → p ∣ zigzag (a+1) → p ∣ zigzag (a+2) →
    ∀ j : ℕ, a+j*D < 3+p^2*D →
      ¬ (p^3 ∣ zigzag (a+j*D) ∧ p^2 ∣ zigzag (a+j*D+1) ∧ p ∣ zigzag (a+j*D+2))

private theorem add_periods {q T start : ℕ} (per : ∀ n, start ≤ n →
    zigzag (n+T) ≡ zigzag n [MOD q]) (b : ℕ) (hb : start ≤ b) (j : ℕ) :
    zigzag (b+j*T) ≡ zigzag b [MOD q] := by
  induction j with
  | zero => simp only [Nat.zero_mul,Nat.add_zero]; rfl
  | succ j ih =>
    rw [Nat.succ_mul,← Nat.add_assoc]
    exact (per (b+j*T) (by omega)).trans ih

private theorem reduce_index {q T start : ℕ} (positive : 0 < T)
    (per : ∀ n, start ≤ n → zigzag (n+T) ≡ zigzag n [MOD q])
    (n : ℕ) (hn : start ≤ n) :
    ∃ b j : ℕ, start ≤ b ∧ b < start+T ∧ b+j*T = n ∧
      ∀ i : ℕ, zigzag (n+i) ≡ zigzag (b+i) [MOD q] := by
  let b := start+(n-start)%T
  let j := (n-start)/T
  have lt := Nat.mod_lt (n-start) positive
  have split : b+j*T = n := by
    dsimp [b,j]
    have decomp := Nat.mod_add_div (n-start) T
    rw [Nat.mul_comm T] at decomp
    omega
  refine ⟨b,j,by dsimp [b]; omega,by dsimp [b]; omega,split,?_⟩
  intro i
  have same : n+i = (b+i)+j*T := by omega
  rw [same]
  apply add_periods per
  dsimp [b]
  omega

private theorem zero_count : zigzag 0 = 1 := by decide

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_2608_27058.main := by
  intro threshold periods sieve p r prime odd hr
  by_contra! short
  let n := r-3
  have length : r = n+3 := by dsimp [n]; omega
  have at_zero : p^3 ∣ zigzag n := by
    have h := threshold p r n prime odd (by omega) (by omega)
    simpa [length] using h
  have at_one : p^2 ∣ zigzag (n+1) := by
    have h := threshold p r (n+1) prime odd (by omega) (by omega)
    simpa [length] using h
  have at_two : p ∣ zigzag (n+2) := by
    have h := threshold p r (n+2) prime odd (by omega) (by omega)
    simpa [length] using h
  let D := Nat.lcm (p-1) 4
  have pp := prime.two_le
  have Dpos : 0 < D := Nat.lcm_pos (by omega) (by decide)
  have p2 : p^2 ∣ p^3 := pow_dvd_pow p (by decide)
  have p3 : p ∣ p^3 := dvd_pow_self _ (by decide)
  have unit : ∀ m, 1 ≤ m → zigzag (m+D) ≡ zigzag m [MOD p] := by
    intro m hm
    simpa [D] using periods p 1 prime odd (Or.inl rfl) m hm
  have cube : ∀ m, 3 ≤ m → zigzag (m+p^2*D) ≡ zigzag m [MOD p^3] := by
    intro m hm
    simpa [D] using periods p 3 prime odd (Or.inr rfl) m hm
  have wrapped : ∃ b : ℕ, b < 3+p^2*D ∧ p^3 ∣ zigzag b ∧ p^2 ∣ zigzag (b+1) ∧ p ∣ zigzag (b+2) := by
    by_cases enough : 3 ≤ n
    · obtain ⟨b,j,_,lt,_,res⟩ := reduce_index (Nat.mul_pos (pow_pos prime.pos _) Dpos) cube n enough
      exact ⟨b,lt,by simpa using ((res 0).dvd_iff dvd_rfl).mp (by simpa using at_zero),
        ((res 1).dvd_iff p2).mp at_one,((res 2).dvd_iff p3).mp at_two⟩
    · exact ⟨n,by omega,at_zero,at_one,at_two⟩
  obtain ⟨b,bound,c0,c1,c2⟩ := wrapped
  have bpos : 1 ≤ b := by
    by_contra! h
    have eq : b = 0 := by omega
    have one := (p3.trans c0)
    rw [eq,zero_count] at one
    exact prime.not_dvd_one one
  obtain ⟨a,j,lo,hi,split,res⟩ := reduce_index Dpos unit b bpos
  have z0 : p ∣ zigzag a := by simpa using ((res 0).dvd_iff dvd_rfl).mp (by simpa using p3.trans c0)
  have z1 := ((res 1).dvd_iff dvd_rfl).mp ((dvd_pow_self p (by decide : 2 ≠ 0)).trans c1)
  have z2 := ((res 2).dvd_iff dvd_rfl).mp c2
  subst b
  exact sieve p prime odd a lo (by omega) z0 z1 z2 j bound ⟨c0,c1,c2⟩

end OMA.R_arxiv_2608_27058_R1
