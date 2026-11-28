import OMAStatements.S_oeis_a323912

-- Dirichlet-ring argument: with E = 2ε - ζ, the hypotheses say a * (2φ - id) = 1, c * φ = 1,
-- H * E = 1 and B * E = ζ. Since φ * E = 2φ - id, a = c * H; since ζ * φ = id and
-- (id·μ) * id = 1, c = (id·μ) * ζ and B = ζ * H, so a = (id·μ) * B.

namespace OMA.A323912
open ArithmeticFunction

def af (u : ℕ → ℤ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else u n, by simp⟩

lemma af_apply (u : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) : af u n = u n := by
  show (if n = 0 then 0 else u n) = u n
  rw [if_neg hn]

lemma conv (u v : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) :
    (af u * af v) n = ∑ d ∈ n.divisors, u d * v (n / d) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => af u x * af v y)]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hq : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_ne_zero hd0)).ne'
  rw [af_apply u hd0, af_apply v hq]

lemma split (n : ℕ) (_hn : 2 ≤ n) (f : ℕ → ℤ) :
    ∑ d ∈ n.divisors, f d = ∑ d ∈ n.properDivisors, f d + f n := by
  rw [← Nat.cons_self_properDivisors (by omega), Finset.sum_cons]; ring

def E : ℕ → ℤ := fun n => if n = 1 then 1 else -1

lemma E_proper {n d : ℕ} (hd : d ∈ n.properDivisors) : E (n / d) = -1 := by
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨⟨k, rfl⟩, hlt⟩ := hd
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hlt
    · exact h
  rw [Nat.mul_div_cancel_left _ hd0, E, if_neg]
  rintro rfl; simp at hlt

lemma ext_pos (f g : ArithmeticFunction ℤ) (h : ∀ n, n ≠ 0 → f n = g n) : f = g := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact h n hn.ne'

/-- `u * E = 1` for a sequence with `u 1 = 1` and `u n = ∑ proper u d` for `n ≥ 2`. -/
lemma rec_E (u : ℕ → ℤ) (r : ℤ) (h1 : u 1 = 1)
    (h : ∀ n, 2 ≤ n → u n = r + ∑ d ∈ n.properDivisors, u d) :
    ∀ n, n ≠ 0 → (af u * af E) n = if n = 1 then 1 else r := by
  intro n hn
  rw [conv _ _ hn]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    simp [E, h1]
  · rw [split n h2, if_neg (by omega), h n h2, Finset.sum_congr rfl (fun d hd => by rw [E_proper hd]),
      Nat.div_self (by omega), E, if_pos rfl]
    simp [Finset.sum_neg_distrib]

end OMA.A323912

open OMA.A323912 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a323912.main := by
  intro a c H B ⟨ha1, ha⟩ hc ⟨hH1, hH⟩ ⟨hB1, hB⟩ n hn
  set Φ := af (fun n => (Nat.totient n : ℤ))
  set Z := af (fun _ => 1)
  set I := af (fun n => (n : ℤ))
  set G := af (fun n => 2 * (Nat.totient n : ℤ) - (n : ℤ))
  set M := af (fun d => (d : ℤ) * moebius d)
  -- translations
  have hA : af a * G = 1 := by
    apply ext_pos; intro n hn
    rw [conv _ _ hn, one_apply]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      simp [ha1]
    · rw [split n h2, if_neg (by omega), ha n h2, Nat.div_self (by omega)]
      simp only [Nat.totient_one, Nat.cast_one]
      rw [← Finset.sum_congr rfl (fun d _ => mul_comm _ _)]
      ring
  have hC : af c * Φ = 1 := by
    apply ext_pos; intro n hn
    rw [conv _ _ hn, one_apply, hc n (Nat.pos_of_ne_zero hn)]
  have hHE : af H * af E = 1 := by
    apply ext_pos; intro n hn
    rw [rec_E H 0 hH1 (fun n h => by rw [hH n h]; ring) n hn, one_apply]
  have hBE : af B * af E = Z := by
    apply ext_pos; intro n hn
    rw [rec_E B 1 hB1 hB n hn, af_apply _ hn]
    split_ifs <;> rfl
  have hZΦ : Z * Φ = I := by
    apply ext_pos; intro n hn
    rw [conv _ _ hn, af_apply _ hn]
    simp only [one_mul]
    rw [Nat.sum_div_divisors n (fun d => (Nat.totient d : ℤ))]
    exact_mod_cast Nat.sum_totient n
  have hΦE : Φ * af E = G := by
    apply ext_pos; intro n hn
    rw [conv _ _ hn, af_apply _ hn]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      simp [E]
    · rw [split n h2, Finset.sum_congr rfl (fun d hd => by rw [E_proper hd]),
        Nat.div_self (by omega), E, if_pos rfl]
      have hs := Nat.sum_totient n
      have : (∑ d ∈ n.divisors, (Nat.totient d : ℤ)) = n := by exact_mod_cast hs
      rw [split n h2] at this
      simp only [mul_neg, mul_one, Finset.sum_neg_distrib]
      linarith
  have hMI : M * I = 1 := by
    apply ext_pos; intro n hn
    rw [conv _ _ hn, one_apply]
    have : ∑ d ∈ n.divisors, (d : ℤ) * moebius d * ((n / d : ℕ) : ℤ) =
        (n : ℤ) * ∑ d ∈ n.divisors, moebius d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
      have h' : ((n / d : ℕ) : ℤ) * d = n := by exact_mod_cast this
      linear_combination moebius d * h'
    rw [this]
    have hm := DFunLike.congr_fun moebius_mul_coe_zeta n
    rw [coe_mul_zeta_apply, one_apply] at hm
    rw [hm]
    split_ifs with h1 <;> simp [h1]
  -- algebra
  have hG : G = Φ * af E := hΦE.symm
  have key1 : af a = af c * af H := by
    calc af a = af a * (af c * Φ * (af H * af E)) := by rw [hC, hHE]; ring
      _ = (af a * G) * (af c * af H) := by rw [hG]; ring
      _ = af c * af H := by rw [hA]; ring
  have hMZ : M * Z = af c := by
    calc M * Z = M * Z * (af c * Φ) := by rw [hC]; ring
      _ = (M * (Z * Φ)) * af c := by ring
      _ = af c := by rw [hZΦ, hMI]; ring
  have hBZ : af B = Z * af H := by
    calc af B = af B * (af H * af E) := by rw [hHE]; ring
      _ = (af B * af E) * af H := by ring
      _ = Z * af H := by rw [hBE]
  have key2 : af a = M * af B := by
    rw [key1, hBZ, ← hMZ]; ring
  have hn0 : n ≠ 0 := by omega
  constructor
  · have := DFunLike.congr_fun key1 n
    rwa [af_apply _ hn0, conv _ _ hn0] at this
  · have := DFunLike.congr_fun key2 n
    rwa [af_apply _ hn0, conv _ _ hn0] at this

