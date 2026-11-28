import FormalConjectures.Wikipedia.SierpinskiNumber
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# The extended Sierpiński problem via two companion problems and the composite search

Selfridge’s conjecture handles coefficients below 78557. The prime Sierpiński
problem handles prime coefficients below 271129. This leaves composite coefficients
strictly between 78557 and 271129.
For the eight rows of J. W. Leventhal, *Partial coverings and conditions for Sierpiński
candidates*, Parabola 60 (2024), §4, we check the exponent progressions, rule out their initial
segments, and give a necessary and sufficient fixed-base modular test. The remaining
composite coefficients form a separate prime-certificate task.
-/

-- Credit: @yuka30240
namespace OMA.R_SierpinskiNumber_extended_sierpinski_problem_R2

private theorem three_nonresidue {N : ℕ} (hp : N.Prime) (h4 : N % 4 = 1) (h3 : N % 3 = 2) :
    (3 : ZMod N) ^ (N / 2) = -1 := by
  let : Fact N.Prime := ⟨hp⟩
  have hr := legendreSym.quadratic_reciprocity_one_mod_four (q := 3) h4 (by decide)
  have hmod : (N : ℤ) % 3 = 2 := by omega
  have hv : legendreSym 3 (N : ℤ) = -1 := by
    rw [legendreSym.mod]
    change legendreSym 3 ((N : ℤ) % 3) = -1
    rw [hmod]
    apply (legendreSym.eq_neg_one_iff 3).mpr
    decide +kernel
  change legendreSym 3 (N : ℤ) = legendreSym N 3 at hr
  have he := legendreSym.eq_pow N 3
  rw [← hr, hv] at he
  simpa using he.symm

private theorem square_chain (N k m : ℕ) :
    (fun x : ℕ => x ^ 2 % N)^[m] (3 ^ k % N) ≡ (3 ^ k) ^ (2 ^ m) [MOD N] := by
  induction m with
  | zero => simpa using Nat.mod_modEq (3 ^ k) N
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ 2 m, pow_mul]
    exact (Nat.mod_modEq _ _).trans (ih.pow 2)

private theorem chain_lt {N : ℕ} (hN : 0 < N) (k m : ℕ) :
    (fun x : ℕ => x ^ 2 % N)^[m] (3 ^ k % N) < N := by
  cases m with
  | zero => exact Nat.mod_lt _ hN
  | succ m => rw [Function.iterate_succ_apply']; exact Nat.mod_lt _ hN

private theorem chain_of_prime {k m : ℕ} (hk : 3 < k) (hk3 : ¬ 3 ∣ k) (hm : 1 ≤ m)
    (hp : (k * 2 ^ (m + 1) + 1).Prime) :
    let N := k * 2 ^ (m + 1) + 1
    (fun x : ℕ => x ^ 2 % N)^[m] (3 ^ k % N) = N - 1 := by
  let N := k * 2 ^ (m + 1) + 1
  change (fun x : ℕ => x ^ 2 % N)^[m] (3 ^ k % N) = N - 1
  have hN : 3 < N := by
    dsimp [N]
    have := Nat.le_mul_of_pos_right k (Nat.two_pow_pos (m + 1))
    omega
  have h4 : N % 4 = 1 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hform : N = (k * 2 ^ i) * 4 + 1 := by dsimp [N]; rw [show 1 + i + 1 = i + 2 by omega, pow_add]; ring
    rw [hform]; omega
  have hprod : ¬ 3 ∣ k * 2 ^ (m + 1) :=
    (Nat.prime_three.not_dvd_mul hk3 (fun h => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)))
  have hN3 : ¬ 3 ∣ N := by
    intro hd
    rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
  have h3 : N % 3 = 2 := by dsimp [N] at hN3 ⊢; omega
  have he := three_nonresidue hp h4 h3
  have half : N / 2 = k * 2 ^ m := by simp only [N, pow_succ, ← Nat.mul_assoc]; omega
  change (3 : ZMod N) ^ (N / 2) = -1 at he
  rw [half, pow_mul] at he
  have hd : N ∣ (3 ^ k) ^ (2 ^ m) + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [he, neg_add_cancel]
  have hc := (square_chain N k m).add_right 1
  have h := Nat.modEq_zero_iff_dvd.mp (hc.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  have := chain_lt (by omega : 0 < N) k m
  have := Nat.le_of_dvd (Nat.succ_pos _) h
  omega

-- The generalized Fermat divisor argument of @desenyon (extended problem, R1)
-- bounds every prime factor below by 2 ^ (m + 1) + 1.
private theorem prime_of_chain {k m : ℕ} (hk : 0 < k) (hsize : k < 2 ^ (m + 1))
    (hc : let N := k * 2 ^ (m + 1) + 1
          (fun x : ℕ => x ^ 2 % N)^[m] (3 ^ k % N) = N - 1) :
    (k * 2 ^ (m + 1) + 1).Prime := by
  let N := k * 2 ^ (m + 1) + 1
  have hpos : 1 < N := by simpa [N] using Nat.mul_pos hk (Nat.two_pow_pos (m + 1))
  have eqn := (square_chain N k m).symm.add_right 1
  change (fun x : ℕ => x ^ 2 % N)^[m] (3 ^ k % N) = N - 1 at hc
  rw [hc, Nat.sub_add_cancel (by omega)] at eqn
  have hd := Nat.modEq_zero_iff_dvd.mp (eqn.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl N)))
  let p := N.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hdiv : p ∣ N := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    rintro heq
    rw [heq] at hdiv
    dsimp [N] at hdiv
    rw [pow_succ, ← Nat.mul_assoc] at hdiv
    omega
  obtain ⟨u, hu⟩ := Nat.pow_pow_add_primeFactors_one_lt hp hp2 (hdiv.trans hd)
  have hne : u ≠ 0 := by rintro rfl; simp at hu; exact hp.ne_one hu
  have hpbig : 2 ^ (m + 1) < p := by
    have := Nat.le_mul_of_pos_left (2 ^ (m + 1)) (by omega : 0 < u)
    omega
  by_contra hn
  have hs : p ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hn
  dsimp [N] at hs
  nlinarith [Nat.mul_le_mul (by omega : k ≤ p - 1) (by omega : 2 ^ (m + 1) ≤ p - 1),
    Nat.sub_add_cancel (by omega : 1 ≤ p)]


private theorem prime_residue {k m r n : ℕ} (hkp : 241 < k) (hm : 0 < m)
    (cover : ∀ j : Fin m, j.val = r ∨
      ∃ p ∈ ([3, 5, 7, 13, 17, 19, 37, 73, 109, 241] : List ℕ),
        2 ^ m ≡ 1 [MOD p] ∧ p ∣ k * 2 ^ j.val + 1)
    (hp : (k * 2 ^ n + 1).Prime) : n % m = r := by
  rcases cover ⟨n % m, Nat.mod_lt _ hm⟩ with hr | ⟨p, hmem, hper, hdiv⟩
  · exact hr
  · have he : (2 : ℕ) ^ n ≡ 2 ^ (n % m) [MOD p] := by
      conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul]
      simpa using (hper.pow (n / m)).mul_right (2 ^ (n % m))
    have hd := Nat.modEq_zero_iff_dvd.mp
      (((he.mul_left k).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr hdiv))
    have bounds : 1 < p ∧ p ≤ 241 := by fin_cases hmem <;> decide
    have := Nat.le_mul_of_pos_right k (Nat.two_pow_pos n)
    rcases hp.eq_one_or_self_of_dvd p hd with h | h <;> omega

-- Blocked iteration keeps the kernel stack shallow. A proper gcd already certifies most
-- of the initial terms, so only the rest need modular squaring.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem prefix_certificates : ∀ c ∈ ([(91549,24,6), (131179,36,2), (163187,24,15), (200749,24,18),
    (209611,24,8), (227723,24,13), (229673,36,33), (238411,12,0)] : List (ℕ × ℕ × ℕ)),
    ∀ t : Fin 128,
    let n := c.2.1 * t.val + c.2.2
    let N := c.1 * 2 ^ n + 1
    let d := N.gcd (Nat.factorial 384)
    (1 < d ∧ d < N) ∨
      (2 ≤ n ∧
        let sq := fun x : ℕ => x ^ 2 % N
        (sq^[64])^[(n - 1) / 64] (sq^[(n - 1) % 64] (3 ^ c.1 % N)) ≠ N - 1) := by
  decide +kernel


/-- For each historical composite candidate, all possible prime exponents are on the
listed progression. The first 128 terms of each progression are composite. Beyond
them, quadratic reciprocity makes three a suitable base in every row. -/
theorem candidate_search_iff (c : ℕ × ℕ × ℕ) (hc : c ∈ ([(91549, 24, 6), (131179, 36, 2), (163187, 24, 15), (200749, 24, 18),
      (209611, 24, 8), (227723, 24, 13), (229673, 36, 33), (238411, 12, 0)] : List (ℕ × ℕ × ℕ))) :
    (∃ n : ℕ, (c.1 * 2 ^ n + 1).Prime) ↔
    ∃ t : ℕ, let n := c.2.1 * (128 + t) + c.2.2
             let N := c.1 * 2 ^ n + 1
             (fun x : ℕ => x ^ 2 % N)^[n - 1] (3 ^ c.1 % N) = N - 1 := by
  let rows := ([(91549, 24, 6), (131179, 36, 2), (163187, 24, 15), (200749, 24, 18),
      (209611, 24, 8), (227723, 24, 13), (229673, 36, 33), (238411, 12, 0)] : List (ℕ × ℕ × ℕ))
  have facts : ∀ e ∈ rows, 241 < e.1 ∧ e.1 < 2 ^ 19 ∧ ¬ 3 ∣ e.1 ∧ 0 < e.2.1 := by decide
  obtain ⟨hk, hsize, hk3, hm⟩ := facts c hc
  have table : ∀ e ∈ rows, ∀ j : Fin e.2.1, j.val = e.2.2 ∨
      ∃ p ∈ ([3, 5, 7, 13, 17, 19, 37, 73, 109, 241] : List ℕ),
        2 ^ e.2.1 ≡ 1 [MOD p] ∧ p ∣ e.1 * 2 ^ j.val + 1 := by decide +kernel
  constructor
  · rintro ⟨n, hp⟩
    have hr := prime_residue hk hm (table c hc) hp
    have hn : c.2.1 * (n / c.2.1) + c.2.2 = n := hr ▸ Nat.div_add_mod n c.2.1
    have ht : 128 ≤ n / c.2.1 := by
      by_contra! h
      have cert := prefix_certificates c hc ⟨n / c.2.1, h⟩
      dsimp only at cert
      rw [hn] at cert
      rcases cert with ⟨h1, h2⟩ | ⟨h2, bad⟩
      · rcases hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left _ (Nat.factorial 384)) with he | he <;> omega
      · have en : n - 1 + 1 = n := by omega
        have eqn := chain_of_prime (m := n - 1) (by omega : 3 < c.1) hk3 (by omega) (en ▸ hp)
        dsimp only at eqn
        rw [en] at eqn
        apply bad
        rwa [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.div_add_mod]
    have hlarge := Nat.le_mul_of_pos_left (n / c.2.1) hm
    have en : n - 1 + 1 = n := by omega
    refine ⟨n / c.2.1 - 128, ?_⟩
    simp only [show 128 + (n / c.2.1 - 128) = n / c.2.1 by omega, hn]
    have eqn := chain_of_prime (m := n - 1) (by omega : 3 < c.1) hk3 (by omega) (en ▸ hp)
    simpa only [en] using eqn
  · rintro ⟨t, cert⟩
    let n := c.2.1 * (128 + t) + c.2.2
    have hge : 19 ≤ n := by
      have := Nat.le_mul_of_pos_left (128 + t) hm
      dsimp [n]; omega
    have en : n - 1 + 1 = n := by omega
    refine ⟨n, ?_⟩
    have hs := hsize.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hge)
    have hp := prime_of_chain (k := c.1) (m := n - 1) (by omega) (en ▸ hs) (by simpa only [en] using cert)
    simpa only [en] using hp

/-- The least Sierpiński number, the companion Selfridge problem. -/
def H1 : Prop := IsLeast {k : ℕ | k.IsSierpinskiNumber} 78557

/-- The least prime Sierpiński number, the companion prime Sierpiński problem. -/
def H2 : Prop := IsLeast {k : ℕ | k.IsSierpinskiNumber ∧ k.Prime} 271129

/-- Supply the archived prime witnesses for the other odd composite coefficients in the gap. -/
def H3 : Prop :=
  ∀ k : ℕ, 78557 < k → k < 271129 → ¬ 2 ∣ k → ¬ k.Prime →
    k ∉ ([91549, 131179, 163187, 200749, 209611, 227723, 229673, 238411] : List ℕ) →
    ∃ n : ℕ, (k * 2 ^ n + 1).Prime

/-- Find one successful base-three square chain per row, starting after its verified prefix. -/
def H4 : Prop :=
  ∀ c ∈ ([(91549, 24, 6), (131179, 36, 2), (163187, 24, 15), (200749, 24, 18),
      (209611, 24, 8), (227723, 24, 13), (229673, 36, 33), (238411, 12, 0)] : List (ℕ × ℕ × ℕ)),
    ∃ t : ℕ, let n := c.2.1 * (128 + t) + c.2.2
             let N := c.1 * 2 ^ n + 1
             (fun x : ℕ => x ^ 2 % N)^[n - 1] (3 ^ c.1 % N) = N - 1

theorem main : H1 → H2 → H3 → H4 → type_of% @SierpinskiNumber.extended_sierpinski_problem := by
  intro least leastPrime archive search
  have uniqueBelow {k : ℕ} (hk : k.IsSierpinskiNumber) (hlt : k < 271129) : k = 78557 := by
    have hlo := least.2 hk
    by_contra hne
    have hcomp : ¬ k.Prime := fun hp => (not_le_of_gt hlt) (leastPrime.2 ⟨hk, hp⟩)
    let rows := ([(91549, 24, 6), (131179, 36, 2), (163187, 24, 15), (200749, 24, 18),
      (209611, 24, 8), (227723, 24, 13), (229673, 36, 33), (238411, 12, 0)] : List (ℕ × ℕ × ℕ))
    by_cases hm : k ∈ rows.map Prod.fst
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
      obtain ⟨n, hn⟩ := (candidate_search_iff c hc).mpr (search c hc)
      exact (hk.2 n).2 hn
    · obtain ⟨n, hn⟩ := archive k (by omega) hlt hk.1 hcomp hm
      exact (hk.2 n).2 hn
  refine ⟨⟨leastPrime.1.1, 78557, least.1, by decide⟩, ?_⟩
  rintro k ⟨hk, j, hj, hjk⟩
  by_contra! hlt
  have := uniqueBelow hk hlt
  have := uniqueBelow hj (hjk.trans hlt)
  omega

/-- All four component statements also follow from the proposed rank. In particular
the search with a fixed base and a cutoff captures every remaining candidate. -/
theorem necessary (rank : type_of% @SierpinskiNumber.extended_sierpinski_problem) :
    H1 ∧ H2 ∧ H3 ∧ H4 := by
  have self := SierpinskiNumber.selfridge_78557
  have uniqueBelow {k : ℕ} (hk : k.IsSierpinskiNumber) (hlt : k < 271129) : k = 78557 := by
    rcases lt_trichotomy k 78557 with h | h | h
    · have := rank.2 ⟨self, k, hk, h⟩
      omega
    · exact h
    · have := rank.2 ⟨hk, 78557, self, h⟩
      omega
  have witness {k : ℕ} (hodd : ¬ 2 ∣ k) (hlo : 78557 < k) (hlt : k < 271129) :
      ∃ n : ℕ, (k * 2 ^ n + 1).Prime := by
    by_contra! h
    have hs : k.IsSierpinskiNumber := ⟨hodd, fun n =>
      ⟨by simpa using Nat.mul_pos (by omega : 0 < k) (Nat.two_pow_pos n), h n⟩⟩
    have := uniqueBelow hs hlt
    omega
  refine ⟨⟨self, ?_⟩, ⟨⟨rank.1.1, by norm_num⟩, ?_⟩, ?_, ?_⟩
  · intro k hk
    by_contra! h
    have := uniqueBelow hk (by omega)
    omega
  · rintro k ⟨hs, hp⟩
    by_contra! h
    have he := uniqueBelow hs h
    exact (by norm_num : ¬ Nat.Prime 78557) (he ▸ hp)
  · intro k hlo hlt hodd _ _
    exact witness hodd hlo hlt
  · intro c hc
    have bounds : ∀ e ∈ ([(91549, 24, 6), (131179, 36, 2), (163187, 24, 15), (200749, 24, 18),
        (209611, 24, 8), (227723, 24, 13), (229673, 36, 33), (238411, 12, 0)] : List (ℕ × ℕ × ℕ)),
        ¬ 2 ∣ e.1 ∧ 78557 < e.1 ∧ e.1 < 271129 := by decide
    obtain ⟨ho, hlo, hlt⟩ := bounds c hc
    exact (candidate_search_iff c hc).mp (witness ho hlo hlt)

end OMA.R_SierpinskiNumber_extended_sierpinski_problem_R2
