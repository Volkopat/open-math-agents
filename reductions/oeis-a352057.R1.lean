import OMAStatements.S_oeis_a352057

-- Reduction of A352057. Credit: @Pixelstorm44
namespace OMA.R_oeis_a352057_R1

open OMA.S_oeis_a352057

/-- Removing one decimal place preserves the digit condition, even after reaching zero. -/
lemma peel {u d : ℕ} (h : NonzeroDigitsAre u d) :
    (∃ b : Fin 2, u % 10 = d * b.val) ∧ NonzeroDigitsAre (u / 10) d := by
  by_cases hu : u = 0
  · subst u
    exact ⟨⟨0, by simp⟩, by simpa using h⟩
  unfold NonzeroDigitsAre at h
  rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hu] at h
  constructor
  · rcases h _ List.mem_cons_self with hz | he
    · exact ⟨0, by simpa using hz⟩
    · exact ⟨1, by simpa using he⟩
  · exact fun _ hx => h _ (List.mem_cons_of_mem _ hx)

lemma index_equation {m n : ℕ} (h : m = n * (n+1) / 2) :
    m * 2 = n * (n+1) := by
  rw [h, Nat.div_mul_cancel (Nat.two_dvd_mul_add_one _)]

lemma square_witness {m : ℕ} (h : IsTriangular m) :
    ∃ x : ℕ, x^2 = 8*m+1 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨2*n+1, by nlinarith [index_equation hn]⟩

/-- The larger of two consecutive factors is at least 5^k. Cancelling this
power from their product bounds the possible exponents for each fixed core. -/
lemma exponent_bound {u k : ℕ} (hu : 0 < u) (h : IsTriangular (10^k*u)) :
    5^k ≤ 2 * 2^k * u + 1 := by
  obtain ⟨n, hn⟩ := h
  have he := index_equation hn
  rw [show (10:ℕ) = 5*2 by decide, mul_pow] at he
  have hnpos : 0 < n := by
    by_contra! hz
    have hn0 : n = 0 := by omega
    simp [hn0] at he
    omega
  have hp : Prime (5:ℕ) := Nat.prime_iff.mp (by decide)
  have hd : 5^k ∣ n*(n+1) :=
    ⟨2^k*u*2, by rw [← he]; ring⟩
  have hle : 5^k ≤ n+1 := by
    by_cases h5 : 5 ∣ n
    · have h5' : ¬5 ∣ n+1 := by omega
      exact (Nat.le_of_dvd hnpos (hp.pow_dvd_of_dvd_mul_right k h5' hd)).trans (by omega)
    · exact Nat.le_of_dvd (by omega) (hp.pow_dvd_of_dvd_mul_left k h5 hd)
  have hprod : 5^k*n ≤ 5^k*(2*2^k*u) := by
    calc
      5^k*n ≤ (n+1)*n := Nat.mul_le_mul_right _ hle
      _ = 5^k*(2*2^k*u) := by nlinarith [he]
  have hnle := Nat.le_of_mul_le_mul_left hprod (by positivity : 0 < (5:ℕ)^k)
  omega

set_option maxHeartbeats 4000000 in
lemma small_core_table : ∀ d : Fin 10, ∀ a b c e f : Fin 2, ∀ k : Fin 21,
    let u := d.val * (1 + 10*a.val + 100*b.val + 1000*c.val + 10000*e.val + 100000*f.val)
    let m := 10^k.val * u
    d.val = 5 ∨ m ≤ 600060 ∨ (8*m+1).sqrt ^ 2 ≠ 8*m+1 := by
  decide +kernel
set_option maxHeartbeats 1000000 in
lemma suffix_table : ∀ d : Fin 10, ∀ a b : Fin 2, ∀ r : Fin 125,
    let v := d.val * (1+10*a.val+100*b.val)
    d.val ≠ 0 → d.val ≠ 5 → (8*v+1)%125 = r.val^2%125 →
    d.val = 1 ∨ d.val = 6 ∨ v = 3 := by
  decide +kernel

/-- The first six places of a normalized core, allowing leading zeroes. -/
lemma core_places {u d : ℕ} (hu : ¬10 ∣ u) (hd : NonzeroDigitsAre u d) :
    ∃ a b c e f : Fin 2,
      u = 10^6 * (u/1000000) +
        d*(1+10*a.val+100*b.val+1000*c.val+10000*e.val+100000*f.val) ∧
      u = 1000*(u/1000) + d*(1+10*a.val+100*b.val) ∧ u%10 = d := by
  obtain ⟨⟨z, hz⟩, h₁⟩ := peel hd
  obtain ⟨⟨a, ha⟩, h₂⟩ := peel h₁
  obtain ⟨⟨b, hb⟩, h₃⟩ := peel h₂
  obtain ⟨⟨c, hc⟩, h₄⟩ := peel h₃
  obtain ⟨⟨e, he⟩, h₅⟩ := peel h₄
  obtain ⟨⟨f, hf⟩, _⟩ := peel h₅
  have units : u % 10 = d := by
    fin_cases z <;> simp_all
    omega
  refine ⟨a, b, c, e, f, ?_, ?_, units⟩ <;>
    simp only [Nat.div_div_eq_div_mul] at * <;> ring_nf at * <;> omega

lemma small_core {u d k : ℕ} (hu : ¬10 ∣ u) (hs : u < 1000000)
    (hd : NonzeroDigitsAre u d) (hne : d ≠ 5)
    (ht : IsTriangular (10^k*u)) : 10^k*u ≤ 600060 := by
  obtain ⟨a,b,c,e,f,hv,_,hmod⟩ := core_places hu hd
  have hu' : 0 < u := by by_contra! hz; simp [show u = 0 by omega] at hu
  have bound := exponent_bound hu' ht
  have hpow : (2:ℕ)^k * 2^k ≤ 2^k * (2*u+1) := by
    calc
      _ = (2*2)^k := (mul_pow _ _ _).symm
      _ ≤ 5^k := Nat.pow_le_pow_left (by decide) _
      _ ≤ _ := by nlinarith [pow_pos (by decide : 0 < 2) k]
  have hk : k < 21 := by
    have h := Nat.le_of_mul_le_mul_left hpow (by positivity : 0 < (2:ℕ)^k)
    by_contra! hh
    have h' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at h'
    omega
  have hv' := Nat.div_eq_of_lt hs
  simp only [hv', mul_zero, zero_add] at hv
  have htab := small_core_table ⟨d, by omega⟩ a b c e f ⟨k, hk⟩
  dsimp only at htab
  rw [← hv] at htab
  obtain ⟨x,hx⟩ := square_witness ht
  have root := Nat.sqrt_eq' x
  rw [hx] at root
  exact (htab.resolve_left hne).resolve_right (by simp [root, hx])

/-- For a candidate with nonzero units digit the square test modulo 125
forces a final 1 or 6, or the three-place suffix 003. -/
lemma unit_suffix {u d : ℕ} (hu : ¬10 ∣ u) (hd : NonzeroDigitsAre u d)
    (h0 : d ≠ 0) (h5 : d ≠ 5) (ht : IsTriangular u) :
    d = 1 ∨ d = 6 ∨ u % 1000 = 3 := by
  obtain ⟨a,b,_,_,_,_,hv,hm⟩ := core_places hu hd
  obtain ⟨x,hx⟩ := square_witness ht
  let v := d*(1+10*a.val+100*b.val)
  have hres : (8*v+1)%125 = (x%125)^2%125 := by
    rw [← Nat.pow_mod, hx]
    change (8*(d*(1+10*a.val+100*b.val))+1)%125 = _
    omega
  have test := suffix_table ⟨d, by omega⟩ a b ⟨x%125, by omega⟩ h0 h5 hres
  rcases test with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · change d*(1+10*a.val+100*b.val) = 3 at h
    exact Or.inr (Or.inr (by omega))

/-- Square obstruction for normalized cores without trailing zeroes. -/
def H1 : Prop := ∀ u d : ℕ, 1000000 ≤ u → u%10 = d → d ≠ 0 → d ≠ 5 →
  NonzeroDigitsAre u d → (d = 1 ∨ d = 6 ∨ u%1000 = 3) →
  ∀ x : ℕ, x^2 ≠ 8*u+1

/-- For each larger normalized core only finitely many positive exponents
satisfy the displayed bound. -/
def H2 : Prop := ∀ u d k : ℕ, 1000000 ≤ u → u%10 = d → d ≠ 0 → d ≠ 5 →
  NonzeroDigitsAre u d → 0 < k → 5^k ≤ 2*2^k*u+1 →
  ∀ x : ℕ, x^2 ≠ 8*(10^k*u)+1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a352057.main := by
  intro h₁ h₂
  constructor
  · refine ⟨⟨1095, by decide⟩, 6, by decide, by decide, ?_⟩
    have digits : Nat.digits 10 600060 = [0,6,0,0,0,6] := by decide
    intro x hx
    simp [digits] at hx
    tauto
  · rintro m ⟨ht, d, hd0, hd5, hd⟩
    by_cases hm : m = 0
    · omega
    obtain ⟨k,u,hu,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm 10 (by decide)
    have pos : 0 < u := by by_contra! hz; simp [show u = 0 by omega] at hu
    have digits : NonzeroDigitsAre u d := by
      intro x hx
      apply hd
      rw [Nat.digits_base_pow_mul (by decide : 1 < 10) pos]
      exact List.mem_append_right _ hx
    by_cases hsmall : u < 1000000
    · exact small_core hu hsmall digits hd5 ht
    have hbig : 1000000 ≤ u := by omega
    obtain ⟨_,_,_,_,_,_,_,hmod⟩ := core_places hu digits
    obtain ⟨x,hx⟩ := square_witness ht
    cases k with
    | zero =>
      simp only [pow_zero, one_mul] at ht hx
      exact False.elim (h₁ u d hbig hmod hd0 hd5 digits (unit_suffix hu digits hd0 hd5 ht) x hx)
    | succ j =>
      exact False.elim (h₂ u d (j+1) hbig hmod hd0 hd5 digits (by omega)
        (exponent_bound pos ht) x hx)

end OMA.R_oeis_a352057_R1
