import OMAReductions.R_Erdos985_erdos_985_R1_H2_R1
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Checked initial prime-root certificates and the higher-order cases

For every eligible modulus below 32768 the checked stream provides a prime
witness. The proof interprets the stream by scanning each integer in each
512-position interval. A factorial gcd test cannot reject a prime in the
range where it is used. Witnesses are checked by binary modular powers and
the complete prime-factor list of the group order.

The remaining moduli are partitioned by whether the order has exactly four
or at least five distinct prime factors. Each remaining input asks for a
prime witness at most 223, as indicated by a separate exploratory computation.
-/

namespace PrimitiveRootCertificate

open Classical (choose choose_spec)

private theorem squarePower_data : ∃ power : ℕ → ℕ → ℕ → ℕ → ℕ, power =
    (fun modulus depth => Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
      (fun _ _ => 1 % modulus)
      (fun _ rec a n =>
        if n = 0 then 1 % modulus else
          let half := rec a (n/2)
          let twice := (half*half) % modulus
          if n%2 = 0 then twice else (twice*(a%modulus)) % modulus)
      depth) := ⟨_, rfl⟩

private theorem squarePower_zero (m a n : ℕ) :
    choose squarePower_data m 0 a n = 1 % m := by
  rw [choose_spec squarePower_data]
  rfl

private theorem squarePower_succ (m depth a n : ℕ) :
    choose squarePower_data m (depth+1) a n =
      (if n = 0 then 1 % m else
        let half := choose squarePower_data m depth a (n/2)
        let twice := (half*half) % m
        if n%2 = 0 then twice else (twice*(a%m)) % m) := by
  rw [choose_spec squarePower_data]

theorem squarePower_eq (m depth a n : ℕ) (fit : n < 2^depth) :
    choose squarePower_data m depth a n = a^n % m := by
  induction depth generalizing n with
  | zero =>
    have h0 : n=0 := by simpa using fit
    subst n
    simp only [squarePower_zero, pow_zero]
  | succ d ih =>
    by_cases nzero : n=0
    · subst n
      simp [squarePower_succ]
    have hhalf : n/2 < 2^d := by rw [pow_succ] at fit; omega
    simp only [squarePower_succ, if_neg nzero, ih _ hhalf]
    have hredu : ((a^(n/2) % m) * (a^(n/2) % m)) % m =
        (a^(n/2)*a^(n/2)) % m := (Nat.mul_mod _ _ _).symm
    rw [hredu, ← pow_add]
    split
    · rename_i even
      have he : n/2+n/2 = n := by omega
      simp [he]
    · rename_i odd
      rw [← Nat.mul_mod, ← pow_succ]
      have he : n/2+n/2+1 = n := by omega
      simp [he]

private theorem witness_data : ∃ witness : ℕ → ℕ → Bool, witness =
    (fun p q => decide q.Prime && decide (q < p) &&
      (p-1).primeFactorsList.all (fun s => choose squarePower_data p 27 q ((p-1)/s) != 1)) :=
  ⟨_, rfl⟩

theorem witness_sound {p q : ℕ} (lt : p < 10^8) (h : choose witness_data p q = true) :
    q.Prime ∧ q < p ∧ ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1 := by
  simp only [choose_spec witness_data, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hprime,hless⟩,hpow⟩ := h
  refine ⟨hprime,hless,?_⟩
  intro s hs
  have hh := (List.all_eq_true.mp hpow) s (List.mem_toFinset.mp hs)
  have hf : (p-1)/s < 2^27 := by
    apply (Nat.div_le_self _ _).trans_lt
    exact (Nat.sub_le p 1).trans_lt (lt.trans (by decide))
  rw [squarePower_eq p 27 q _ hf] at hh
  exact bne_iff_ne.mp hh

private theorem candidates_data : ∃ candidates : List ℕ, candidates =
    [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,
      113,127,131,137,139,149] := ⟨_, rfl⟩

private theorem wheel_data : ∃ wheel : ℕ, wheel =
  402387260077093773543702433923003985719374864210714632543799910429938512398629020592044208486969404800479988610197196058631666872994808558901323829669944590997424504087073759918823627727188732519779505950995276120874975462497043601418278094646496291056393887437886487337119181045825783647849977012476632889835955735432513185323958463075557409114262417474349347553428646576611667797396668820291207379143853719588249808126867838374559731746136085379534524221586593201928090878297308431392844403281231558611036976801357304216168747609675871348312025478589320767169132448426236131412508780208000261683151027341827977704784635868170164365024153691398281264810213092761244896359928705114964975419909342221566832572080821333186116811553615836546984046708975602900950537616475847728421889679646244945160765353408198901385442487984959953319101723355556602139450399736280750137837615307127761926849034352625200015888535147331611702103968175921510907788019393178114194545257223865541461062892187960223838971476088506276862967146674697562911234082439208160153780889893964518263243671616762179168909779911903754031274622289988005195444414282012187361745992642956581746628302955570299024324153181617210465832036786906117260158783520751516284225540265170483304226143974286933061690897968482590125458327168226458066526769958652682272807075781391858178889652208164348344825993266043367660176999612831860788386150279465955131156552036093988180612138558600301435694527224206344631797460594682573103790084024432438465657245014402821885252470935190620929023136493273497565513958720559654228749774011413346962715422845862377387538230483865688976461927383814900140767310446640259899490222221765904339901886018566526485061799702356193897017860040811889729918311021171229845901641921068884387121855646124960798722908519296819372388642614839657382291123125024186649353143970137428531926649875337218940694281434118520158014123344828015051399694290153483077644569099073152433278288269864602789864321139083506217095002597389863554277196742822248757586765752344220207573630569498825087968928162753848863396909959826280956121450994871701244516461260379029309120889086942028510640182154399457156805941872748998094254742173582401063677404595741785160829230135358081840096996372524230560855903700624271243416909004153690105933983835777939410970027753472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := ⟨_, rfl⟩

set_option maxRecDepth 5000 in
theorem wheel_eq : choose wheel_data = Nat.factorial 1000 := by
  rw [choose_spec wheel_data]
  decide +kernel

private theorem plausiblePrime_data : ∃ plausible : ℕ → Bool, plausible =
    (fun p => if p ≤ 1000 then decide p.Prime else p.gcd (choose wheel_data) == 1) :=
  ⟨_, rfl⟩

theorem prime_plausible {p : ℕ} (hp : p.Prime) : choose plausiblePrime_data p = true := by
  simp only [choose_spec plausiblePrime_data]
  split
  · exact decide_eq_true hp
  · rename_i hl
    have h := hp.coprime_factorial_of_lt (by omega : 1000 < p)
    rw [wheel_eq, beq_iff_eq]
    exact h

private theorem eligible_data : ∃ eligible : ℕ → Bool, eligible =
    (fun p => choose plausiblePrime_data p && decide (4 ≤ (p-1).primeFactors.card)) :=
  ⟨_, rfl⟩

theorem eligible_true {p : ℕ} (hp : p.Prime) (many : 4 ≤ (p-1).primeFactors.card) :
    choose eligible_data p = true := by
  simp only [choose_spec eligible_data, prime_plausible hp, decide_eq_true many, Bool.and_self]

private theorem packed_data : ∃ packed : ℕ → ℕ → ℕ → Bool, packed =
    (fun size => Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
      (fun _ _ => true)
      (fun _ rec start code =>
        if choose eligible_data start then
          choose witness_data start ((choose candidates_data)[code%64]?.getD 0) &&
            rec (start+1) (code/64)
        else rec (start+1) code)
      size) := ⟨_, rfl⟩

private theorem packed_succ (size start code : ℕ) :
    choose packed_data (size+1) start code =
      if choose eligible_data start then
        choose witness_data start ((choose candidates_data)[code%64]?.getD 0) &&
          choose packed_data size (start+1) (code/64)
      else choose packed_data size (start+1) code := by
  rw [choose_spec packed_data]

theorem packed_sound (size start code p : ℕ) (h : choose packed_data size start code = true)
    (hlo : start ≤ p) (hhi : p < start+size) (hp : p.Prime) (lt : p < 10^8)
    (many : 4 ≤ (p-1).primeFactors.card) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1 := by
  induction size generalizing start code with
  | zero => omega
  | succ n ih =>
    by_cases he : p=start
    · subst p
      simp only [packed_succ, eligible_true hp many, if_true, Bool.and_eq_true] at h
      exact ⟨_, witness_sound lt h.1⟩
    simp only [packed_succ] at h
    split at h
    · simp only [Bool.and_eq_true] at h
      exact ih _ _ h.2 (by omega) (by omega)
    · exact ih _ _ h (by omega) (by omega)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_0 : ∃ code, choose packed_data 512 0 code = true := by
  refine ⟨0x40040, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_1 : ∃ code, choose packed_data 512 512 code = true := by
  refine ⟨0x283086001001040, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_2 : ∃ code, choose packed_data 512 1024 code = true := by
  refine ⟨0xc4001143001000083, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_3 : ∃ code, choose packed_data 512 1536 code = true := by
  refine ⟨0x420421c0040044, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_4 : ∃ code, choose packed_data 512 2048 code = true := by
  refine ⟨0x70060010010c10c0040, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_5 : ∃ code, choose packed_data 512 2560 code = true := by
  refine ⟨0x14000408200400f0400c3, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_6 : ∃ code, choose packed_data 512 3072 code = true := by
  refine ⟨0x30c00812812801811c40c10c4, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_7 : ∃ code, choose packed_data 512 3584 code = true := by
  refine ⟨0x40000140000043080280, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_8 : ∃ code, choose packed_data 512 4096 code = true := by
  refine ⟨0x1040813410410c0001004046, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_9 : ∃ code, choose packed_data 512 4608 code = true := by
  refine ⟨0x1000400c4041001001040, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_10 : ∃ code, choose packed_data 512 5120 code = true := by
  refine ⟨0x41c51010410420430c1006005, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_11 : ∃ code, choose packed_data 512 5632 code = true := by
  refine ⟨0x830c70810402801060c400000f, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_12 : ∃ code, choose packed_data 512 6144 code = true := by
  refine ⟨0x90440000411801c1184080041, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_13 : ∃ code, choose packed_data 512 6656 code = true := by
  refine ⟨0x300108a00500004a0c00000000c4, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_14 : ∃ code, choose packed_data 512 7168 code = true := by
  refine ⟨0x30002c50000c00000831c31c0006, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_15 : ∃ code, choose packed_data 512 7680 code = true := by
  refine ⟨0x180003040341141040283044, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_16 : ∃ code, choose packed_data 512 8192 code = true := by
  refine ⟨0x2410c21402000411c1000, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_17 : ∃ code, choose packed_data 512 8704 code = true := by
  refine ⟨0x401c1188043040040200080040084200080, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_18 : ∃ code, choose packed_data 512 9216 code = true := by
  refine ⟨0x40001040041203001003005, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_19 : ∃ code, choose packed_data 512 9728 code = true := by
  refine ⟨0xc02800410080000401011011c5, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_20 : ∃ code, choose packed_data 512 10240 code = true := by
  refine ⟨0x30420c20400020c20c10c0, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_21 : ∃ code, choose packed_data 512 10752 code = true := by
  refine ⟨0x1820830010440420010000800c0181, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_22 : ∃ code, choose packed_data 512 11264 code = true := by
  refine ⟨0x10482000020c2044083083001041, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_23 : ∃ code, choose packed_data 512 11776 code = true := by
  refine ⟨0x3004042155101083000, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_24 : ∃ code, choose packed_data 512 12288 code = true := by
  refine ⟨0x1412401002c40420450c32440c0, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_25 : ∃ code, choose packed_data 512 12800 code = true := by
  refine ⟨0x110100108200b0c008d, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_26 : ∃ code, choose packed_data 512 13312 code = true := by
  refine ⟨0x20c8107203081040105080049000, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_27 : ∃ code, choose packed_data 512 13824 code = true := by
  refine ⟨0x821c10040c5001003049, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_28 : ∃ code, choose packed_data 512 14336 code = true := by
  refine ⟨0x100b00000404014100a040000, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_29 : ∃ code, choose packed_data 512 14848 code = true := by
  refine ⟨0x10840c4103004000001047000000, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_30 : ∃ code, choose packed_data 512 15360 code = true := by
  refine ⟨0x90040000810c8080181081048180, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_31 : ∃ code, choose packed_data 512 15872 code = true := by
  refine ⟨0x30010010c30801480c2004, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_32 : ∃ code, choose packed_data 512 16384 code = true := by
  refine ⟨0x460040011050401001c10c00c1, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_33 : ∃ code, choose packed_data 512 16896 code = true := by
  refine ⟨0x40011c00c31c00420031800010000c6, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_34 : ∃ code, choose packed_data 512 17408 code = true := by
  refine ⟨0x432c0047001081047140041041001, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_35 : ∃ code, choose packed_data 512 17920 code = true := by
  refine ⟨0x1440491000c32400c12020440010000810c0, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_36 : ∃ code, choose packed_data 512 18432 code = true := by
  refine ⟨0x180080001105049200140041, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_37 : ∃ code, choose packed_data 512 18944 code = true := by
  refine ⟨0x10440c2040104081000006000100, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_38 : ∃ code, choose packed_data 512 19456 code = true := by
  refine ⟨0x40050400c2105000145007004, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_39 : ∃ code, choose packed_data 512 19968 code = true := by
  refine ⟨0x1046083100042245007041041209, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_40 : ∃ code, choose packed_data 512 20480 code = true := by
  refine ⟨0x431050000800810c0081040102, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_41 : ∃ code, choose packed_data 512 20992 code = true := by
  refine ⟨0x50821c00070030000070c7000004, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_42 : ∃ code, choose packed_data 512 21504 code = true := by
  refine ⟨0x30460850c40c204a0401c01c0084002, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_43 : ∃ code, choose packed_data 512 22016 code = true := by
  refine ⟨0x4e1c30410c0085183001, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_44 : ∃ code, choose packed_data 512 22528 code = true := by
  refine ⟨0x830012030000432432c5045003181040, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_45 : ∃ code, choose packed_data 512 23040 code = true := by
  refine ⟨0x204004110f001001081081040, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_46 : ∃ code, choose packed_data 512 23552 code = true := by
  refine ⟨0x504a5000800800420431040401810c0042, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_47 : ∃ code, choose packed_data 512 24064 code = true := by
  refine ⟨0xc40430400460040c50020c4, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_48 : ∃ code, choose packed_data 512 24576 code = true := by
  refine ⟨0x42000040100049000080000045, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_49 : ∃ code, choose packed_data 512 25088 code = true := by
  refine ⟨0x1042800c10c11c5043000040081, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_50 : ∃ code, choose packed_data 512 25600 code = true := by
  refine ⟨0xc00c01431010813410430001c40c0, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_51 : ∃ code, choose packed_data 512 26112 code = true := by
  refine ⟨0x43041045140001101085, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_52 : ∃ code, choose packed_data 512 26624 code = true := by
  refine ⟨0x10000040010c4080042001209143, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_53 : ∃ code, choose packed_data 512 27136 code = true := by
  refine ⟨0x30001870c30c6083089180186, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_54 : ∃ code, choose packed_data 512 27648 code = true := by
  refine ⟨0x10011c20011400402820c3001042041, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_55 : ∃ code, choose packed_data 512 28160 code = true := by
  refine ⟨0x1102140040002002040008005000101, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_56 : ∃ code, choose packed_data 512 28672 code = true := by
  refine ⟨0x4210004000b047, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_57 : ∃ code, choose packed_data 512 29184 code = true := by
  refine ⟨0x418304b181000005007042043005003, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_58 : ∃ code, choose packed_data 512 29696 code = true := by
  refine ⟨0x2001001289140000081043140086000, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_59 : ∃ code, choose packed_data 512 30208 code = true := by
  refine ⟨0x10000420c2144081080041044040, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_60 : ∃ code, choose packed_data 512 30720 code = true := by
  refine ⟨0x31451c30011411030000060400c0002, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_61 : ∃ code, choose packed_data 512 31232 code = true := by
  refine ⟨0xc11010410030c32800830c3203, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_62 : ∃ code, choose packed_data 512 31744 code = true := by
  refine ⟨0x10860840401420000c800001b, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem check_63 : ∃ code, choose packed_data 512 32256 code = true := by
  refine ⟨0x10810410c318000208008000a, ?_⟩
  simp only [choose_spec packed_data, choose_spec eligible_data, choose_spec plausiblePrime_data,
    choose_spec wheel_data, choose_spec witness_data, choose_spec candidates_data,
    choose_spec squarePower_data]
  decide +kernel

private theorem checkedBlock (i : ℕ) (hi : i < 64) :
    ∃ code, choose packed_data 512 (i*512) code = true := by
  interval_cases i
  · exact check_0
  · exact check_1
  · exact check_2
  · exact check_3
  · exact check_4
  · exact check_5
  · exact check_6
  · exact check_7
  · exact check_8
  · exact check_9
  · exact check_10
  · exact check_11
  · exact check_12
  · exact check_13
  · exact check_14
  · exact check_15
  · exact check_16
  · exact check_17
  · exact check_18
  · exact check_19
  · exact check_20
  · exact check_21
  · exact check_22
  · exact check_23
  · exact check_24
  · exact check_25
  · exact check_26
  · exact check_27
  · exact check_28
  · exact check_29
  · exact check_30
  · exact check_31
  · exact check_32
  · exact check_33
  · exact check_34
  · exact check_35
  · exact check_36
  · exact check_37
  · exact check_38
  · exact check_39
  · exact check_40
  · exact check_41
  · exact check_42
  · exact check_43
  · exact check_44
  · exact check_45
  · exact check_46
  · exact check_47
  · exact check_48
  · exact check_49
  · exact check_50
  · exact check_51
  · exact check_52
  · exact check_53
  · exact check_54
  · exact check_55
  · exact check_56
  · exact check_57
  · exact check_58
  · exact check_59
  · exact check_60
  · exact check_61
  · exact check_62
  · exact check_63

theorem checkedPrefix (p : ℕ) (hp : p.Prime) (small : p < 32768) (large : p < 10^8)
    (many : 4 ≤ (p-1).primeFactors.card) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1 := by
  let i := p/512
  have hi : i < 64 := by dsimp [i]; omega
  obtain ⟨code, hcode⟩ := checkedBlock i hi
  exact packed_sound 512 (i*512) code p hcode
    (by dsimp [i]; omega) (by dsimp [i]; omega) hp large many

end PrimitiveRootCertificate

namespace OMA.R_Erdos985_erdos_985_R1_H2_R1_H2_R1

/-- The larger moduli with exactly four distinct prime factors of the order. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 32768 ≤ p → p < 10^8 → (p-1).primeFactors.card = 4 →
    ∃ q : ℕ, q.Prime ∧ q ≤ 223 ∧ q < p ∧
      ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1

/-- The larger moduli with at least five distinct prime factors of the order. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 32768 ≤ p → p < 10^8 → 5 ≤ (p-1).primeFactors.card →
    ∃ q : ℕ, q.Prime ∧ q ≤ 223 ∧ q < p ∧
      ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1

theorem main : H1 → H2 → OMA.R_Erdos985_erdos_985_R1_H2_R1.H2 := by
  intro four five p hp hupper hcard
  by_cases small : p < 32768
  · exact PrimitiveRootCertificate.checkedPrefix p hp small hupper hcard
  have exist : ∃ q : ℕ, q.Prime ∧ q ≤ 223 ∧ q < p ∧
      ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1 := by
    by_cases he : (p-1).primeFactors.card = 4
    · exact four p hp (by omega) hupper he
    · exact five p hp (by omega) hupper (by omega)
  obtain ⟨q,pr,_,lt,tests⟩ := exist
  exact ⟨q,pr,lt,tests⟩

end OMA.R_Erdos985_erdos_985_R1_H2_R1_H2_R1
