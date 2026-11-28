import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1_H1_R1

/-!
# Proof of OeisA135508.conjecture.R1.H2.R1.H1.R1.H2

Certifies for every prime `q` with `100000 < q <= 500000` the existence of `m : Fin 278`
such that `r = m.val * q - 2` is prime, `5 < r`, `r < q^2`, `r % 3 = 2`, and `q ∣ r + 2`,
using GMP-accelerated primorial-wheel GCD primality verification and compositeness filtering.
-/

-- Proof of step OeisA135508.conjecture.R1.H2.R1.H1.R1.H2
-- Credit: @mvanhorn

section OeisA135508H2Cert

private def wheel : Nat := 0x1578b225e79f3f381a574077542b3f5cb3ade6bff0e3ae9ae88b37273c1609f84c08b89d4398482cc0b2dbc970cfa9fbe87b9939afc726a8d9c9ef3ed33982687a87fe16b11aca66f95e793e6cefe2da57f3d92d3f3461a7f9cfe1fe3477babd948a573a2cfda7dab67520c5f1b17cb929f7f84b887972c20917e990aab15169c0c96672ce652449ca3ecf2d1d0d0fa052bfdccad14a66f0a5ae69eaaaa8a9b3f43855680a708ef13f18979de799e968fe4dd0cace2c362997d5a56888b76e75a8c5c0a1f69da70fabb753b35be9a08bf5430b5dd31cd1772ac2718ed0759d831022ed5d5c977b0984bd793efc6fbb97a672505c5b6b274e2cefaae6581a914d6ee6bbb94f9e53899b82392b1332c59145fce6dd563771317fbd9a5673b089f57acd4d379335f71cb3e8158c34d2c7c62ca94a6ba42c1074e625df7a2557feb7b8d891c9f955a916cb9684e76478b1a323b72b9199796fbd848903b7e4ad655a19db6e0bf3d474fb3b26e9e0ccdbeb96598b2103a96d64b5c1707a8e932b4a3852723f6832b14d3318d1b2164d1caac75ade83170b9a2d4e7dbf949471370b4a96dbd515732328a1d5b74572dff537f4106c9f3b108d56cf3b9206703cd234b320437a6477a0729988046c13fef0783a3c1c7b6b5b2e9f866671f7757c686aa193c1b51e851a166c3b9dc7dfc4adcf19c428fbc69286e16387736fa199a308ee9c2db9778eafd443a7ad4bc1efa7feddeb1e339ded4889358d625a7732aa0e8497d2c6a667620e4205115d22c0a1df00df3fadfaf484479c3ea6b10f4c17f9bc8b4190c4c172f9917c2c6b9d006a85ce8f96dfdbb753334ef781952f1e6c94a926b25395c4133f0d72958486dabb61b4678e9873314c315f4359164a6fa966a7cef398819ce3971330ace042860c002c765ed440aefdc5530737356a0df9b229511401b6bf5cc819df37ef6211becd299a353663422936266b4bd8af5da91705d22341c7d6b8f594f4c5ad4b82ebcf45700f52802d8cfb9e87ac085463c98d9ac69325cd2f6aad9a41ba140cfc8739b1b659f1aec39fdfd5254e68c2e9021ce9befc2a459e942df9910d23d4350416a7cd49b0bbf4397d6e83a113195b89f4cb5c26765904224ec95cf9f18fd4d302ed1d40dc183434c1eb65aef31010544aa745c6c9936dbf98b74432edf03ac20cf9af6bc625aab94095c6ddb4b45eef57946dcaf9ba154a2bc1061351fa0981e0819c1993767c704843829518dbcc692cd067d9d812a5877809de7c21739af9b60f287c9e84961c188b08d88e29a5ced640c09b500982cb5b2d26c4f9b4a118d54ffc917bbe4b42afd50fe23b995feef0a534a17696f2be0cec2b78491006de25cfa34d47387fb44c5cc2417a299e467e75a99425b839b0152210a92cdc7caf5caa64d99d68609b5b5d0d8f8f13e781d6c3cca6ce3856f2f1064a2110c7b582817c4b0ea29b27af9db6179585fec0030eca72a317ecb1c4bc2b36d9df9b12165b6508af6d590947c19a41619808df6a3dc20b9fd0b5d37a003e9bc6c4b1a909ab15f2ffef912d90ae970268e9c1266bca1786ab0e5842a6e441c2bae4e586eba03170825213553fd864d0ec3c60f0364052710a5a2569612fcd32400d703894b02ef3753c312b4d9c3a174fc1dbddf45ef3330f307e4bfe023184fb6afe1472f9d6a1490f5bd2cda8576af32d7dec2fb2ebdea67e0732190adebfd6ab131e508d5103c43e5e9e3852dae84b5a3d056bcf657d3b6a4b6a6e0edf78da1c4dc1b97671c420374e9ffec547127338c4a664f46fffaf8a77afc6deb050499069e0a6de20069b0cb79010b28d5bdb3e9475fe7dd9efaa62b3696f25bffd0e84de34c1b550ca8c4844835cba146986773717fb0d9cb199964f0418895fce18740fe3ec6e05658579196ba99960b98b570c3b0372c8686684c5b56b934ba51f16d506665ae71ba1bd765a5e1b3de5dd3fcfba0ca1aaf0b80a84cf3744a87b92ceb2aacd25abc8d1d1249ffd6de33e1ecdbce183a83ac984aebc2a6dc123daf104730b3da5dc990e9901907be0c17f03523464f41f4e908eb1a465c26b190938c43f2aebd0e1a5691ced94d3395277e7c2e7e62de25aa583e986c25999bf0c8be4a5b2490e23a0471c7b8f58b06b231b23bb172f583e00eaeac16b113a09e07709fa84e25a2e07633dfa989c31cbbd909bc53ce359b2635b4d6c73b1850723952c5a8d400d7394a0b4cc95179957b3e9adab57af9c69d2bfdb45ecdbed00eff75bfda494b3e11e484211bf176b1d9735617ad259a0e065c206902662af751bce43b5f3fac138e24ccee50b1a8becfe146e53a52ec6ec65289e966a07b97c8b244c3181dbf5140ae9640a5fdbf98510cde56f01d5d44c32bcb21854b67f47ad4fb555b5374f6c55737324eb9f14327915d009a615b9e337c283edbd766bb925b808fb9e4173eb258cfb0d92fb4acd4b56c41408427e55566f94f9e8f46e0abeee92257bcb75c705347c764e827fc0eae189578d3dd90fff6bfb4071293dba0c61d335107a9d298254399c54dac8b3e2652b0512ded65a08db8e0393942888397053601d7941593a60b730c39123199689141d43bc80d1408c86d84411aea7057c6acd9d3412937d5ae744886bf53ce17c32286b6b17a80b3c3ff54fea8efe5f61375a1c028076ae1fd65969ae13214770517d156e1afdb3de8ce2c4c086e556e4c02ec6f7f4030ea861785eb9dfee27d7c2ad83f9821d48b96ebc3bcf7cce95a8ba2f552a12a952b8bc0c4dcc3f03eefa41951f9a0b480d0d495fc350dafe0c02a29e06e80a39e618f7ccc61226b084f96241b5f42ce4d755855dbf97e51c61b8c5e9d96db6f2aad3e8b8ff410b7ed0d9d2dae69087967c67993164374fde22bf3bc9ad26e2f8508880af1746a0ae2898455691dbd3504ed432b4d6900a55d7a35938606bd7e9e30e59fffb8bbe8cd328955513db5ef9d7a2ee80d71f841cd069f4e153c9cedc6d4c22d20cb0aa7f0701f346ec8e26636fbd5b5c337ba15352270261e47d10bc53649805db9e5aeed6f1dbaf0ce8142d681d367556959672fa134fd7f3fa

private def qWheel : Nat := 0x159c913c4e9c6b605f7f0665bc6baf7d121c0c5929a06e47615ce59e3834556c4a8ae74f652a624b33857496ad6d5038867e989829a7a016ba95dc29550b24fa5b0b86d53037854337d5ce2abaac2cf9ba19b51c389ddc3d489dbc64f89533cfaaf78a536389d3fc94e792908fa199ef148c772c944f5506ee544e

private def qFacVal : Nat := 0x23e6faddbf3b0e3aaaa66b301e811b28fe50c621ba585c2254e807b6dbad96f99061a106bfd740e70f4807dd6b3f38e213695b7d7323448680ffc28692dd26aa542a0d43cd93387bd7c6ae4fa7e9bb56e42ae3214e607c1d7fb11b3462a3e71498ba91ac46c225564988964c0d52dd573289e706e49528900e3775a5714303a3e4cb69f81e42003447c695a5f09a6d502589f32c2c3ebd2db1be04fa8d4cda37b7f17b9aecff647b8fc55709ff81fef3bfccfb61ebccfd6a764a64f21411e408e65cb0778495e67882a77631eecbe3a3db473a1d7da639fc3e34d6f486d6e94360db635bc588452d074604a88bc0c0b31f8b5c4aa7afe43c689fc372612f8452c113aa64581666c102f9e866a732a792667e2bb2a407ca863f503e0b8fcf363bc0fd63f86b582699bccaa4920a8fa2779044dfcdecb3d72ca6c8b97de2126cab1b3da5e2377fc2a5d430bb26649af447c8b98b2afa67f00d49bbe054867b5c1eb008426763ad97c1125a2b644f92da6605c0e9aef0637ef1fc39e08bde865eaf680b487d7b81ab22703a963192a71e7061f8045ec4f4bb95748a4dff6ebc014933d0924ab22b0d881c3495051dd8b2b3a67df0c2005157132bd50b7e2d77cffb27998b7603d77f2aef572d777f3c115bf5f1fc9a9c397f48710b2c0aa9ce77bd90acceed3c7a6e87c515923b346d51b89918bdce11bafd28893d2c8b13b88944c42a515c79a07aa159468a0ca304ce23f472df0e784529eed0ea09ee24dbe668c020153a19e1600e0ed1cbd636a718e1f66289809ede6e4c3eb22a84cae8a5bab2138fd01ff106543564a0fdf169402e3bf237acc00c16b59b30087adaa28533c285a4b27cc84a814f56bc4cb854499ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

set_option maxRecDepth 8192 in
private lemma qFacVal_eq : qFacVal = Nat.factorial 709 := by decide +kernel

private lemma qWheel_dvd_qFacVal : qWheel ∣ qFacVal :=
  Nat.dvd_of_mod_eq_zero (by decide +kernel)

private lemma qWheel_dvd_fac : qWheel ∣ Nat.factorial 709 :=
  qFacVal_eq ▸ qWheel_dvd_qFacVal

private def looksPrime (r : Nat) : Bool :=
  if r ≤ 12288 then r.minFac == r
  else r ≤ 12288 ^ 2 && Nat.gcd r (wheel % r) == 1

private def search (q : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, k =>
    if k < 278 then
      let r := k * q - 2
      (5 < r && r < q * q && r % 3 == 2 && looksPrime r) || search q n (k + 6)
    else false

private def good (q : Nat) : Bool :=
  if 500000 < q || q ≤ 100000 || q % 2 == 0 || q % 3 == 0 then true
  else Nat.gcd q (qWheel % q) != 1 || search q 48 (if q % 3 == 1 then 1 else 5)

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
private lemma checkWheel (j : Fin 12) :
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
    have hdB : d ≤ 12288 := by
      rw [← Nat.sqrt_eq' 12288]
      exact hds.trans (Nat.sqrt_le_sqrt h.1)
    let j : Fin 12 := ⟨(d - 2) / 1024, by omega⟩
    have ht := block_at (checkWheel j) (x := d) (by dsimp [j]; omega) (by dsimp [j]; omega)
    have hcop := cop.coprime_dvd_left hdvd
    simp only [bne_iff_ne, gcd_remainder] at ht
    exact ht hcop

private def GoalAt (q : ℕ) : Prop :=
  ∃ m : Fin 278, let r := m.val * q - 2
    r.Prime ∧ 5 < r ∧ r < q ^ 2 ∧ r % 3 = 2 ∧ q ∣ r + 2

private lemma search_sound (q n k : ℕ) (h : search q n k = true) : GoalAt q := by
  induction n generalizing k with
  | zero => simp [search] at h
  | succ n ih =>
    unfold search at h
    by_cases hk : k < 278
    · simp only [hk, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      rcases h with ⟨⟨⟨hr, hsq⟩, hmod⟩, hp⟩ | h
      · refine ⟨⟨k, hk⟩, looksPrime_sound hr hp, hr, by simpa [sq] using hsq, hmod, k, ?_⟩
        dsimp only
        rw [Nat.mul_comm q k]
        omega
      · exact ih (k + 6) h
    · simp [hk] at h

private lemma good_sound {q : ℕ} (hp : q.Prime) (hlo : 100000 < q) (hhi : q ≤ 500000)
    (h : good q = true) : GoalAt q := by
  have nd (d : ℕ) (h1 : 1 < d) (h2 : d < q) : q % d ≠ 0 := by
    intro hz
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hz) with e | e <;> omega
  have h2 := nd 2 (by decide) (by omega)
  have h3 := nd 3 (by decide) (by omega)
  simp [good, not_lt.mpr hhi, not_le.mpr hlo, h2, h3] at h
  have copFac : Nat.Coprime q (Nat.factorial 709) := hp.coprime_factorial_of_lt (by omega)
  have cop : Nat.Coprime q qWheel := copFac.coprime_dvd_right qWheel_dvd_fac
  simp [gcd_remainder, show Nat.gcd q qWheel = 1 from cop] at h
  exact search_sound _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
private lemma checked (i : Fin 25) (j : Fin 16) :
    block good 10 (99328 + 1024 * (16 * i.val + j.val)) = true := by
  fin_cases i <;> fin_cases j <;> as_aux_lemma => decide +kernel

end OeisA135508H2Cert

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1_H2_R1_H1_R1.H2 := by
  intro q hp hlo hhi
  let idx := (q - 99328) / 1024
  let i : Fin 25 := ⟨idx / 16, by dsimp [idx]; omega⟩
  let j : Fin 16 := ⟨idx % 16, Nat.mod_lt _ (by decide)⟩
  apply good_sound hp hlo hhi
  apply block_at (checked i j)
  · dsimp [i, j, idx]; omega
  · dsimp [i, j, idx]; omega
