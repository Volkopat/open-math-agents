import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1_H1_R1

/-!
# Proof of OeisA135508.conjecture.R1.H2.R1.H1.R1.H1

Certifies for every prime `q` with `100 < q <= 100000` the existence of `m : Fin 258`
such that `r = m.val * q - 2` is prime, `5 < r`, `r < q^2`, `r % 3 = 2`, and `q ∣ r + 2`,
using GMP-accelerated primorial-wheel GCD primality verification and compositeness filtering.
-/

-- Proof of step OeisA135508.conjecture.R1.H2.R1.H1.R1.H1
-- Credit: @mvanhorn

section OeisA135508H1Cert

private def wheel : Nat := 0x4fe43c99ab1d4b82fb62181608cdf254da35e2509ca1ed2c61a2bc632b4ab01e7665bdc31494e92728925dd7211e8f94b33cf972e2da39b982cb3198b48b74f444d48c40a4286b87bea0b342dd5b00cfd3fe713196fe1a8ef91bfdb256567e83d0f5e4ef8f6f9ff93a21acff3cb617353bc083f1ab635e8507d26ee4308e43ea5d24dde0b1c0b54c1ae384925f2bc1b4283dd5a1d6818e43ed2055fb92d7615f7aeeeb20453336aede273f9dbc43147355bed9561b3167d47f61365a5992721e1c3cd5e6b1b79446b05bc870771d736d4107df5b51059b9a3bff8319130832b54f6820037de9ea7b9cf653b6d1c0d9a37e82d299f2b2116364710c914889f6c5c434731116567cef6d762085c1ce7e7f208db9f843b93d4478594a76af1793d223c27d0702cd452d627568648bad61b1ef7ec587d8ee97c3ad83eef04dd264c0ea1dad1adea22ae802a68734da7e4a1312de6e133630b46620919769a561060cc0caedfd396a9ade2550c1603d29840d68d64c2926fe0d7d245f1819f8ec09ed98e718eb0c68415bd6dbcceb2ae3a354611db9601f72512100a679c9baadc7e2ef50684dae00f67df611174a37f0e0d4ab9828a78c8e5d7a07fd94fd92813231964f0475240b9a774bf08d679d0ff0f27ba0923366a8e3d56f04134f2f87b6acb0e79f4806136de2f7443a0a3d2f3a4716ec861f62dcfc63f58a181987d26ec1c05015a9223b822688cd18e8934197b55f94bd3fbbf956d93c74cb54193fa4235492be0371bac7c60c03b2d3ab16fac739a8b664739ac4334684779568f7ba8358664e5012ef9447d20db63182edebe75ec48aa62444146a198b25836d74d954225debb8bde3fd1fc702db92d856c497cf39a316cdb72d61f205a8eeffbbf4e1c08e4fdc500a6931ff93603bdb5302749b6faa6674a337c963c027a1af07146ea2a7db8fb555d5fc9a6c63def4697757c11e623c79733d1a9e1ed585af2fe3667580230c2bfdb9bb81938dbf0a7cbf93ef619c08baa76

private def qWheel : Nat := 0x1bee87df8814520ab6a2b4ad45a8fafbd9003084538cec6070961c4661ef14c7e3c5c7ee5b67d8887efb4d8c6a49c260548077ba4407a

private def qFacVal : Nat := 0x3b47579addd45a02231a4495a0371ceae5d3c3b713a055874248793cac8c418ba9b42612fc079686510ad546a8f46cffd504ba2c31b22873dd81f27f880770c841f686b85561c504125e80f6d511f82cdbab3a7515ee191f7447259a6f8311ae567586d0682aa5c395a0c14de38e657c9c3e92e7a050c555eb44a73436afb60bfb9dd9845c6d73732eeb0622f4d132e3f8e978f14de4f443057f4677eeb987540997b1f4385ccfc9313ac3feb2177e0a5da21629c69c88c4f5c7e2b41b96242bc68d1a14bbcdd1643eaee410bc4c8a03f6f16e62a6470bb53184d80a7a956cd601530bfd99f337e045b0800000000000000000000000000000000000000000000000000000000000000000000000000000

set_option maxRecDepth 8192 in
private lemma qFacVal_eq : qFacVal = Nat.factorial 317 := by decide +kernel

private lemma qWheel_dvd_qFacVal : qWheel ∣ qFacVal :=
  Nat.dvd_of_mod_eq_zero (by decide +kernel)

private lemma qWheel_dvd_fac : qWheel ∣ Nat.factorial 317 :=
  qFacVal_eq ▸ qWheel_dvd_qFacVal

private def looksPrime (r : Nat) : Bool :=
  if r ≤ 4096 then r.minFac == r
  else r ≤ 4096 ^ 2 && Nat.gcd r (wheel % r) == 1

private def search (q : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, k =>
    if k < 258 then
      let r := k * q - 2
      (5 < r && r < q * q && r % 3 == 2 && looksPrime r) || search q n (k + 6)
    else false

private def good (q : Nat) : Bool :=
  if 100000 < q || q ≤ 100 || q % 2 == 0 || q % 3 == 0 then true
  else if q ≤ 317 then q.minFac != q || search q 44 (if q % 3 == 1 then 1 else 5)
  else Nat.gcd q (qWheel % q) != 1 || search q 44 (if q % 3 == 1 then 1 else 5)

private def block (f : Nat → Bool) : Nat → Nat → Bool
  | 0, a => f a
  | d + 1, a => block f d a && block f d (a + 2 ^ d)

private lemma block_at {f : Nat → Bool} {d a x : Nat} (h : block f d a = true)
    (hlo : a ≤ x) (hhi : x < a + 2 ^ d) : f x = true := by
  induction d generalizing a with
  | zero =>
    have : x = a := by simp at hhi; omega
    exact this ▸ h
  | succ d ih =>
    have hh := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at hhi
    by_cases hmid : x < a + 2 ^ d
    · exact ih hh.1 hlo hmid
    · exact ih hh.2 (by omega) (by omega)

private lemma gcd_remainder (n w : ℕ) : n.gcd (w % n) = n.gcd w := by
  rw [Nat.gcd_comm n (w % n), ← Nat.gcd_rec]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private lemma checkWheel (j : Fin 4) :
    block (fun n => Nat.gcd n (wheel % n) != 1) 10 (2 + 1024 * j.val) = true := by
  fin_cases j <;> as_aux_lemma => decide +kernel

private lemma looksPrime_sound {r : ℕ} (hr : 5 < r) (h : looksPrime r = true) : r.Prime := by
  unfold looksPrime at h
  split at h
  · exact Nat.prime_def_minFac.mpr ⟨by omega, beq_iff_eq.mp h⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, gcd_remainder] at h
    have cop : Nat.Coprime r wheel := h.2
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨by omega, ?_⟩
    intro d hd hds hdvd
    have hdB : d ≤ 4096 := by
      rw [← Nat.sqrt_eq' 4096]
      exact hds.trans (Nat.sqrt_le_sqrt h.1)
    let j : Fin 4 := ⟨(d - 2) / 1024, by omega⟩
    have ht := block_at (checkWheel j) (x := d) (by dsimp [j]; omega) (by dsimp [j]; omega)
    have hcop := cop.coprime_dvd_left hdvd
    simp only [bne_iff_ne, gcd_remainder] at ht
    exact ht hcop

private def GoalAt (q : ℕ) : Prop :=
  ∃ m : Fin 258, let r := m.val * q - 2
    r.Prime ∧ 5 < r ∧ r < q ^ 2 ∧ r % 3 = 2 ∧ q ∣ r + 2

private lemma search_sound (q n k : ℕ) (h : search q n k = true) : GoalAt q := by
  induction n generalizing k with
  | zero => simp [search] at h
  | succ n ih =>
    unfold search at h
    by_cases hk : k < 258
    · simp only [hk, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      rcases h with ⟨⟨⟨hr, hsq⟩, hmod⟩, hp⟩ | h
      · refine ⟨⟨k, hk⟩, looksPrime_sound hr hp, hr, by simpa [sq] using hsq, hmod, k, ?_⟩
        dsimp only
        rw [Nat.mul_comm q k]
        omega
      · exact ih (k + 6) h
    · simp [hk] at h

private lemma good_sound {q : ℕ} (hp : q.Prime) (hlo : 100 < q) (hhi : q ≤ 100000)
    (h : good q = true) : GoalAt q := by
  have nd (d : ℕ) (h1 : 1 < d) (h2 : d < q) : q % d ≠ 0 := by
    intro hz
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hz) with e | e <;> omega
  have h2 := nd 2 (by decide) (by omega)
  have h3 := nd 3 (by decide) (by omega)
  simp [good, not_lt.mpr hhi, not_le.mpr hlo, h2, h3] at h
  split at h
  · simp [hp.minFac_eq] at h
    exact search_sound _ _ _ h
  · rename_i hlarge
    have copFac : Nat.Coprime q (Nat.factorial 317) := hp.coprime_factorial_of_lt (by omega)
    have cop : Nat.Coprime q qWheel := copFac.coprime_dvd_right qWheel_dvd_fac
    simp [gcd_remainder, show Nat.gcd q qWheel = 1 from cop] at h
    exact search_sound _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
private lemma checked (i : Fin 7) (j : Fin 16) :
    block good 10 (0 + 1024 * (16 * i.val + j.val)) = true := by
  fin_cases i <;> fin_cases j <;> as_aux_lemma => decide +kernel

end OeisA135508H1Cert

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1_H2_R1_H1_R1.H1 := by
  intro q hp hlo hhi
  let idx := (q - 0) / 1024
  let i : Fin 7 := ⟨idx / 16, by dsimp [idx]; omega⟩
  let j : Fin 16 := ⟨idx % 16, Nat.mod_lt _ (by decide)⟩
  apply good_sound hp hlo hhi
  apply block_at (checked i j)
  · dsimp [i, j, idx]; omega
  · dsimp [i, j, idx]; omega
