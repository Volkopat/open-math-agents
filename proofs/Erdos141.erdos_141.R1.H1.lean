import OMAReductions.R_Erdos141_erdos_141_R1
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime

-- Step Erdos141.erdos_141.R1.H1: hypothesis H1 of reduction Erdos141.erdos_141.R1
-- Credit: @qu1r0ra
-- H1 := ∀ k : ℕ, 7 ≤ k → k ≤ 10 → ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k

/-!
H1 follows from the ten consecutive primes in arithmetic progression found by Manfred Toplic,
published by Dubner, Forbes, Lygeros, Mizony and Zimmermann, Ten consecutive primes in arithmetic
progression, Math. Comp. 71 (2002), 1323–1328: its first k terms are k consecutive primes in
arithmetic progression for every k ≤ 10.
The certificate below (Lucas primality certificates for the ten 93-digit terms and Fermat or
divisor witnesses for every gap number) is reproduced unchanged from the merged proof
proofs/Erdos141.erdos_141.variants.first_cases.lean, which proves the lengths 3 to 10;
only the final statement differs.
-/

namespace ConsecutivePrimes141

-- Radix-64 modular exponentiation keeps the recursion for 93-digit inputs below 52 steps.
private def residue (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | h+1, a, n => if n = 0 then 1 else
      (a ^ (n % 64) * (residue p h a (n/64)) ^ 64) % p

private theorem cast_residue (p h a n : ℕ) (hn : n < 64^h) :
    (residue p h a n : ZMod p) = (a : ZMod p)^n := by
  induction h generalizing a n with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [this, residue]
  | succ h ih =>
    by_cases hzero : n = 0
    · simp [hzero, residue]
    rw [pow_succ] at hn
    simp only [residue, if_neg hzero, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow,
      ih a (n/64) (by omega), ← pow_mul, ← pow_add]
    congr 1
    omega

private theorem lucas (p a : ℕ) (f : List ℕ) (hf : f.prod = p-1)
    (primeFactors : ∀ q ∈ f, Nat.Prime q)
    (hsize : p < 64^52)
    (full : residue p 52 a (p-1) = 1)
    (partialPowers : ∀ q ∈ f, residue p 52 a ((p-1)/q) % p ≠ 1 % p) : p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · rw [← cast_residue p 52 a (p-1) (by omega), full, Nat.cast_one]
  · intro q hq hd h
    rw [← hf] at hd
    obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (primeFactors r hr)).mp hqr
    have hn := Nat.div_le_self (p-1) q
    rw [← cast_residue p 52 a _ (by omega), ← Nat.cast_one (R := ZMod p)] at h
    exact partialPowers q hr ((ZMod.natCast_eq_natCast_iff ..).mp h)

private theorem composite (n d : ℕ) (hc :
    (1 < d ∧ d < n ∧ n % d = 0) ∨
      (n < 64^52 ∧ residue n 52 2 n % n ≠ 2 % n)) : ¬ n.Prime := by
  intro hp
  rcases hc with ⟨h1, h2, hd⟩ | ⟨hsize, hpow⟩
  · rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hd) with h | h <;> omega
  · let : Fact n.Prime := ⟨hp⟩
    apply hpow
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    rw [cast_residue _ _ _ _ hsize, Nat.cast_ofNat, ZMod.pow_card]


-- The arithmetic checks for each row use only natural-number operations.
private theorem certified (p a : ℕ) (fs : List ℕ) (hf : ∀ q ∈ fs, q.Prime)
    (check : fs.prod = p-1 ∧ p < 64^52 ∧ residue p 52 a (p-1) = 1 ∧
      fs.all (fun q => decide (residue p 52 a ((p-1)/q) % p ≠ 1 % p)) = true) :
    p.Prime :=
  lucas p a fs check.1 hf check.2.1 check.2.2.1
    (fun q hq => of_decide_eq_true (List.all_eq_true.mp check.2.2.2 q hq))

set_option maxRecDepth 4096 in
private theorem p5023 : Nat.Prime 5023 := by
  apply certified _ 3 [2, 3, 3, 3, 3, 31]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5441 : Nat.Prime 5441 := by
  apply certified _ 3 [2, 2, 2, 2, 2, 2, 5, 17]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5557 : Nat.Prime 5557 := by
  apply certified _ 2 [2, 2, 3, 463]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5839 : Nat.Prime 5839 := by
  apply certified _ 6 [2, 3, 7, 139]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5849 : Nat.Prime 5849 := by
  apply certified _ 3 [2, 2, 2, 17, 43]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6037 : Nat.Prime 6037 := by
  apply certified _ 5 [2, 2, 3, 503]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6131 : Nat.Prime 6131 := by
  apply certified _ 2 [2, 5, 613]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6397 : Nat.Prime 6397 := by
  apply certified _ 2 [2, 2, 3, 13, 41]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6917 : Nat.Prime 6917 := by
  apply certified _ 2 [2, 2, 7, 13, 19]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p7027 : Nat.Prime 7027 := by
  apply certified _ 2 [2, 3, 1171]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p7057 : Nat.Prime 7057 := by
  apply certified _ 5 [2, 2, 2, 2, 3, 3, 7, 7]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p7243 : Nat.Prime 7243 := by
  apply certified _ 2 [2, 3, 17, 71]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p7919 : Nat.Prime 7919 := by
  apply certified _ 7 [2, 37, 107]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p8537 : Nat.Prime 8537 := by
  apply certified _ 3 [2, 2, 2, 11, 97]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p8951 : Nat.Prime 8951 := by
  apply certified _ 13 [2, 5, 5, 179]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9011 : Nat.Prime 9011 := by
  apply certified _ 2 [2, 5, 17, 53]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9239 : Nat.Prime 9239 := by
  apply certified _ 19 [2, 31, 149]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9277 : Nat.Prime 9277 := by
  apply certified _ 5 [2, 2, 3, 773]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9689 : Nat.Prime 9689 := by
  apply certified _ 3 [2, 2, 2, 7, 173]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9829 : Nat.Prime 9829 := by
  apply certified _ 10 [2, 2, 3, 3, 3, 7, 13]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9931 : Nat.Prime 9931 := by
  apply certified _ 10 [2, 3, 5, 331]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p10301 : Nat.Prime 10301 := by
  apply certified _ 2 [2, 2, 5, 5, 103]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p10597 : Nat.Prime 10597 := by
  apply certified _ 5 [2, 2, 3, 883]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p10883 : Nat.Prime 10883 := by
  apply certified _ 2 [2, 5441]
  · simp only [List.forall_mem_cons, p5441]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p11657 : Nat.Prime 11657 := by
  apply certified _ 3 [2, 2, 2, 31, 47]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p11927 : Nat.Prime 11927 := by
  apply certified _ 5 [2, 67, 89]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p12263 : Nat.Prime 12263 := by
  apply certified _ 5 [2, 6131]
  · simp only [List.forall_mem_cons, p6131]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p12373 : Nat.Prime 12373 := by
  apply certified _ 2 [2, 2, 3, 1031]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p13309 : Nat.Prime 13309 := by
  apply certified _ 6 [2, 2, 3, 1109]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p13313 : Nat.Prime 13313 := by
  apply certified _ 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p15443 : Nat.Prime 15443 := by
  apply certified _ 2 [2, 7, 1103]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p16069 : Nat.Prime 16069 := by
  apply certified _ 2 [2, 2, 3, 13, 103]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p16421 : Nat.Prime 16421 := by
  apply certified _ 2 [2, 2, 5, 821]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p17203 : Nat.Prime 17203 := by
  apply certified _ 2 [2, 3, 47, 61]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p18047 : Nat.Prime 18047 := by
  apply certified _ 5 [2, 7, 1289]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p23671 : Nat.Prime 23671 := by
  apply certified _ 3 [2, 3, 3, 5, 263]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p23767 : Nat.Prime 23767 := by
  apply certified _ 3 [2, 3, 17, 233]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p23971 : Nat.Prime 23971 := by
  apply certified _ 10 [2, 3, 5, 17, 47]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p24509 : Nat.Prime 24509 := by
  apply certified _ 2 [2, 2, 11, 557]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p26417 : Nat.Prime 26417 := by
  apply certified _ 3 [2, 2, 2, 2, 13, 127]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p28591 : Nat.Prime 28591 := by
  apply certified _ 3 [2, 3, 5, 953]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p28837 : Nat.Prime 28837 := by
  apply certified _ 2 [2, 2, 3, 3, 3, 3, 89]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p30071 : Nat.Prime 30071 := by
  apply certified _ 13 [2, 5, 31, 97]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p32843 : Nat.Prime 32843 := by
  apply certified _ 2 [2, 16421]
  · simp only [List.forall_mem_cons, p16421]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p34127 : Nat.Prime 34127 := by
  apply certified _ 5 [2, 113, 151]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p37003 : Nat.Prime 37003 := by
  apply certified _ 2 [2, 3, 7, 881]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p37337 : Nat.Prime 37337 := by
  apply certified _ 3 [2, 2, 2, 13, 359]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p37489 : Nat.Prime 37489 := by
  apply certified _ 19 [2, 2, 2, 2, 3, 11, 71]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p40627 : Nat.Prime 40627 := by
  apply certified _ 2 [2, 3, 3, 37, 61]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p41681 : Nat.Prime 41681 := by
  apply certified _ 3 [2, 2, 2, 2, 5, 521]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p47809 : Nat.Prime 47809 := by
  apply certified _ 7 [2, 2, 2, 2, 2, 2, 3, 3, 83]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p49019 : Nat.Prime 49019 := by
  apply certified _ 2 [2, 24509]
  · simp only [List.forall_mem_cons, p24509]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p55697 : Nat.Prime 55697 := by
  apply certified _ 3 [2, 2, 2, 2, 59, 59]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p58193 : Nat.Prime 58193 := by
  apply certified _ 3 [2, 2, 2, 2, 3637]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p59791 : Nat.Prime 59791 := by
  apply certified _ 3 [2, 3, 5, 1993]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p63617 : Nat.Prime 63617 := by
  apply certified _ 3 [2, 2, 2, 2, 2, 2, 2, 7, 71]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p64853 : Nat.Prime 64853 := by
  apply certified _ 2 [2, 2, 31, 523]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p66109 : Nat.Prime 66109 := by
  apply certified _ 2 [2, 2, 3, 7, 787]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p73553 : Nat.Prime 73553 := by
  apply certified _ 3 [2, 2, 2, 2, 4597]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p74761 : Nat.Prime 74761 := by
  apply certified _ 19 [2, 2, 2, 3, 5, 7, 89]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p77513 : Nat.Prime 77513 := by
  apply certified _ 3 [2, 2, 2, 9689]
  · simp only [List.forall_mem_cons, p9689]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p82217 : Nat.Prime 82217 := by
  apply certified _ 3 [2, 2, 2, 43, 239]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p84827 : Nat.Prime 84827 := by
  apply certified _ 2 [2, 7, 73, 83]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p90073 : Nat.Prime 90073 := by
  apply certified _ 10 [2, 2, 2, 3, 3, 3, 3, 139]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p92269 : Nat.Prime 92269 := by
  apply certified _ 10 [2, 2, 3, 3, 11, 233]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p93257 : Nat.Prime 93257 := by
  apply certified _ 3 [2, 2, 2, 11657]
  · simp only [List.forall_mem_cons, p11657]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p111341 : Nat.Prime 111341 := by
  apply certified _ 3 [2, 2, 5, 19, 293]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p114649 : Nat.Prime 114649 := by
  apply certified _ 7 [2, 2, 2, 3, 17, 281]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p116959 : Nat.Prime 116959 := by
  apply certified _ 3 [2, 3, 101, 193]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p123731 : Nat.Prime 123731 := by
  apply certified _ 2 [2, 5, 12373]
  · simp only [List.forall_mem_cons, p12373]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p129707 : Nat.Prime 129707 := by
  apply certified _ 2 [2, 64853]
  · simp only [List.forall_mem_cons, p64853]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p133241 : Nat.Prime 133241 := by
  apply certified _ 6 [2, 2, 2, 5, 3331]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p157351 : Nat.Prime 157351 := by
  apply certified _ 21 [2, 3, 5, 5, 1049]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p161779 : Nat.Prime 161779 := by
  apply certified _ 2 [2, 3, 59, 457]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p169199 : Nat.Prime 169199 := by
  apply certified _ 7 [2, 31, 2729]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p169943 : Nat.Prime 169943 := by
  apply certified _ 5 [2, 31, 2741]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p185821 : Nat.Prime 185821 := by
  apply certified _ 10 [2, 2, 3, 5, 19, 163]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p217661 : Nat.Prime 217661 := by
  apply certified _ 3 [2, 2, 5, 10883]
  · simp only [List.forall_mem_cons, p10883]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p229939 : Nat.Prime 229939 := by
  apply certified _ 2 [2, 3, 19, 2017]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p248827 : Nat.Prime 248827 := by
  apply certified _ 2 [2, 3, 113, 367]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p275491 : Nat.Prime 275491 := by
  apply certified _ 10 [2, 3, 3, 5, 3061]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p312553 : Nat.Prime 312553 := by
  apply certified _ 7 [2, 2, 2, 3, 3, 3, 1447]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p318691 : Nat.Prime 318691 := by
  apply certified _ 3 [2, 3, 3, 5, 3541]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p337969 : Nat.Prime 337969 := by
  apply certified _ 13 [2, 2, 2, 2, 3, 3, 2347]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p339887 : Nat.Prime 339887 := by
  apply certified _ 5 [2, 169943]
  · simp only [List.forall_mem_cons, p169943]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p360293 : Nat.Prime 360293 := by
  apply certified _ 2 [2, 2, 90073]
  · simp only [List.forall_mem_cons, p90073]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p403061 : Nat.Prime 403061 := by
  apply certified _ 3 [2, 2, 5, 7, 2879]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p440239 : Nat.Prime 440239 := by
  apply certified _ 3 [2, 3, 239, 307]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p471313 : Nat.Prime 471313 := by
  apply certified _ 5 [2, 2, 2, 2, 3, 3, 3, 1091]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p475141 : Nat.Prime 475141 := by
  apply certified _ 2 [2, 2, 3, 5, 7919]
  · simp only [List.forall_mem_cons, p7919]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p492673 : Nat.Prime 492673 := by
  apply certified _ 5 [2, 2, 2, 2, 2, 2, 2, 3, 1283]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p695171 : Nat.Prime 695171 := by
  apply certified _ 2 [2, 5, 7, 9931]
  · simp only [List.forall_mem_cons, p9931]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p720653 : Nat.Prime 720653 := by
  apply certified _ 2 [2, 2, 67, 2689]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p771233 : Nat.Prime 771233 := by
  apply certified _ 3 [2, 2, 2, 2, 2, 7, 11, 313]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p930157 : Nat.Prime 930157 := by
  apply certified _ 2 [2, 2, 3, 77513]
  · simp only [List.forall_mem_cons, p77513]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p952111 : Nat.Prime 952111 := by
  apply certified _ 3 [2, 3, 3, 5, 71, 149]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p965357 : Nat.Prime 965357 := by
  apply certified _ 3 [2, 2, 7, 23, 1499]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1083707 : Nat.Prime 1083707 := by
  apply certified _ 2 [2, 13, 41681]
  · simp only [List.forall_mem_cons, p41681]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1305599 : Nat.Prime 1305599 := by
  apply certified _ 11 [2, 7, 93257]
  · simp only [List.forall_mem_cons, p93257]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1652947 : Nat.Prime 1652947 := by
  apply certified _ 2 [2, 3, 275491]
  · simp only [List.forall_mem_cons, p275491]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1858211 : Nat.Prime 1858211 := by
  apply certified _ 10 [2, 5, 185821]
  · simp only [List.forall_mem_cons, p185821]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2018591 : Nat.Prime 2018591 := by
  apply certified _ 7 [2, 5, 7, 28837]
  · simp only [List.forall_mem_cons, p28837]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2161759 : Nat.Prime 2161759 := by
  apply certified _ 3 [2, 3, 360293]
  · simp only [List.forall_mem_cons, p360293]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2380463 : Nat.Prime 2380463 := by
  apply certified _ 5 [2, 7, 193, 881]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2544811 : Nat.Prime 2544811 := by
  apply certified _ 3 [2, 3, 5, 84827]
  · simp only [List.forall_mem_cons, p84827]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2591189 : Nat.Prime 2591189 := by
  apply certified _ 2 [2, 2, 659, 983]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2611199 : Nat.Prime 2611199 := by
  apply certified _ 13 [2, 1305599]
  · simp only [List.forall_mem_cons, p1305599]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p4037183 : Nat.Prime 4037183 := by
  apply certified _ 5 [2, 2018591]
  · simp only [List.forall_mem_cons, p2018591]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p4062701 : Nat.Prime 4062701 := by
  apply certified _ 2 [2, 2, 5, 5, 40627]
  · simp only [List.forall_mem_cons, p40627]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p4676323 : Nat.Prime 4676323 := by
  apply certified _ 3 [2, 3, 7, 111341]
  · simp only [List.forall_mem_cons, p111341]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p4975823 : Nat.Prime 4975823 := by
  apply certified _ 5 [2, 67, 71, 523]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5182379 : Nat.Prime 5182379 := by
  apply certified _ 2 [2, 2591189]
  · simp only [List.forall_mem_cons, p2591189]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p7152083 : Nat.Prime 7152083 := by
  apply certified _ 2 [2, 7, 487, 1049]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p15982339 : Nat.Prime 15982339 := by
  apply certified _ 2 [2, 3, 1499, 1777]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p16467721 : Nat.Prime 16467721 := by
  apply certified _ 11 [2, 2, 2, 3, 5, 109, 1259]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p18675439 : Nat.Prime 18675439 := by
  apply certified _ 3 [2, 3, 881, 3533]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p19189553 : Nat.Prime 19189553 := by
  apply certified _ 3 [2, 2, 2, 2, 751, 1597]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p21651121 : Nat.Prime 21651121 := by
  apply certified _ 13 [2, 2, 2, 2, 3, 3, 5, 30071]
  · simp only [List.forall_mem_cons, p30071]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p26360903 : Nat.Prime 26360903 := by
  apply certified _ 5 [2, 461, 28591]
  · simp only [List.forall_mem_cons, p28591]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p30164033 : Nat.Prime 30164033 := by
  apply certified _ 3 [2, 2, 2, 2, 2, 2, 471313]
  · simp only [List.forall_mem_cons, p471313]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p31569287 : Nat.Prime 31569287 := by
  apply certified _ 5 [2, 7, 503, 4483]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p37937261 : Nat.Prime 37937261 := by
  apply certified _ 2 [2, 2, 5, 179, 10597]
  · simp only [List.forall_mem_cons, p10597]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p43243117 : Nat.Prime 43243117 := by
  apply certified _ 2 [2, 2, 3, 7, 587, 877]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p46694521 : Nat.Prime 46694521 := by
  apply certified _ 14 [2, 2, 2, 3, 3, 5, 129707]
  · simp only [List.forall_mem_cons, p129707]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p56784023 : Nat.Prime 56784023 := by
  apply certified _ 5 [2, 4703, 6037]
  · simp only [List.forall_mem_cons, p6037]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p60534853 : Nat.Prime 60534853 := by
  apply certified _ 2 [2, 2, 3, 7, 720653]
  · simp only [List.forall_mem_cons, p720653]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p60703897 : Nat.Prime 60703897 := by
  apply certified _ 5 [2, 2, 2, 3, 11, 229939]
  · simp only [List.forall_mem_cons, p229939]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p79944847 : Nat.Prime 79944847 := by
  apply certified _ 5 [2, 3, 17, 31, 131, 193]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p97169879 : Nat.Prime 97169879 := by
  apply certified _ 7 [2, 13, 101, 37003]
  · simp only [List.forall_mem_cons, p37003]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p183577111 : Nat.Prime 183577111 := by
  apply certified _ 3 [2, 3, 5, 499, 12263]
  · simp only [List.forall_mem_cons, p12263]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p238771427 : Nat.Prime 238771427 := by
  apply certified _ 2 [2, 17, 757, 9277]
  · simp only [List.forall_mem_cons, p9277]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p247956283 : Nat.Prime 247956283 := by
  apply certified _ 2 [2, 3, 3, 3, 7, 71, 9239]
  · simp only [List.forall_mem_cons, p9239]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p319779389 : Nat.Prime 319779389 := by
  apply certified _ 2 [2, 2, 79944847]
  · simp only [List.forall_mem_cons, p79944847]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p329668739 : Nat.Prime 329668739 := by
  apply certified _ 2 [2, 7, 79, 347, 859]
  · simp only [List.forall_mem_cons]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p335730821 : Nat.Prime 335730821 := by
  apply certified _ 2 [2, 2, 5, 1087, 15443]
  · simp only [List.forall_mem_cons, p15443]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p357852113 : Nat.Prime 357852113 := by
  apply certified _ 5 [2, 2, 2, 2, 29, 771233]
  · simp only [List.forall_mem_cons, p771233]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p461096189 : Nat.Prime 461096189 := by
  apply certified _ 10 [2, 2, 7, 16467721]
  · simp only [List.forall_mem_cons, p16467721]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1058408119 : Nat.Prime 1058408119 := by
  apply certified _ 3 [2, 3, 3, 173, 339887]
  · simp only [List.forall_mem_cons, p339887]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1081539587 : Nat.Prime 1081539587 := by
  apply certified _ 2 [2, 499, 1083707]
  · simp only [List.forall_mem_cons, p1083707]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1110031619 : Nat.Prime 1110031619 := by
  apply certified _ 2 [2, 47, 103, 114649]
  · simp only [List.forall_mem_cons, p114649]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1625900707 : Nat.Prime 1625900707 := by
  apply certified _ 5 [2, 3, 3, 17, 17, 312553]
  · simp only [List.forall_mem_cons, p312553]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2109160373 : Nat.Prime 2109160373 := by
  apply certified _ 2 [2, 2, 11, 29, 1652947]
  · simp only [List.forall_mem_cons, p1652947]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2695073261 : Nat.Prime 2695073261 := by
  apply certified _ 3 [2, 2, 5, 11, 149, 82217]
  · simp only [List.forall_mem_cons, p82217]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2854582189 : Nat.Prime 2854582189 := by
  apply certified _ 2 [2, 2, 3, 7243, 32843]
  · simp only [List.forall_mem_cons, p7243, p32843]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p3262224011 : Nat.Prime 3262224011 := by
  apply certified _ 6 [2, 5, 17, 19189553]
  · simp only [List.forall_mem_cons, p19189553]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p3308813021 : Nat.Prime 3308813021 := by
  apply certified _ 3 [2, 2, 5, 17, 17, 43, 13313]
  · simp only [List.forall_mem_cons, p13313]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5390146523 : Nat.Prime 5390146523 := by
  apply certified _ 2 [2, 2695073261]
  · simp only [List.forall_mem_cons, p2695073261]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6823638763 : Nat.Prime 6823638763 := by
  apply certified _ 2 [2, 3, 17203, 66109]
  · simp only [List.forall_mem_cons, p66109, p17203]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9135179189 : Nat.Prime 9135179189 := by
  apply certified _ 2 [2, 2, 307, 313, 23767]
  · simp only [List.forall_mem_cons, p23767]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p11197579487 : Nat.Prime 11197579487 := by
  apply certified _ 5 [2, 23, 131, 1858211]
  · simp only [List.forall_mem_cons, p1858211]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p12231997963 : Nat.Prime 12231997963 := by
  apply certified _ 2 [2, 3, 6397, 318691]
  · simp only [List.forall_mem_cons, p6397, p318691]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p12882676069 : Nat.Prime 12882676069 := by
  apply certified _ 2 [2, 2, 3, 3, 357852113]
  · simp only [List.forall_mem_cons, p357852113]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p16174127069 : Nat.Prime 16174127069 := by
  apply certified _ 2 [2, 2, 11, 23, 15982339]
  · simp only [List.forall_mem_cons, p15982339]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p22829695829 : Nat.Prime 22829695829 := by
  apply certified _ 2 [2, 2, 17, 335730821]
  · simp only [List.forall_mem_cons, p335730821]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p27565782029 : Nat.Prime 27565782029 := by
  apply certified _ 2 [2, 2, 55697, 123731]
  · simp only [List.forall_mem_cons, p55697, p123731]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p37907731723 : Nat.Prime 37907731723 := by
  apply certified _ 2 [2, 3, 7, 7, 797, 161779]
  · simp only [List.forall_mem_cons, p161779]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p47053325621 : Nat.Prime 47053325621 := by
  apply certified _ 2 [2, 2, 5, 7, 353, 952111]
  · simp only [List.forall_mem_cons, p952111]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p102678983629 : Nat.Prime 102678983629 := by
  apply certified _ 6 [2, 2, 3, 13, 23, 71, 403061]
  · simp only [List.forall_mem_cons, p403061]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p146783975557 : Nat.Prime 146783975557 := by
  apply certified _ 2 [2, 2, 3, 12231997963]
  · simp only [List.forall_mem_cons, p12231997963]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p164433225403 : Nat.Prime 164433225403 := by
  apply certified _ 3 [2, 3, 3, 9135179189]
  · simp only [List.forall_mem_cons, p9135179189]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p198528781261 : Nat.Prime 198528781261 := by
  apply certified _ 7 [2, 2, 3, 5, 3308813021]
  · simp only [List.forall_mem_cons, p3308813021]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p218447926987 : Nat.Prime 218447926987 := by
  apply certified _ 2 [2, 3, 17, 71, 30164033]
  · simp only [List.forall_mem_cons, p30164033]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p248692063469 : Nat.Prime 248692063469 := by
  apply certified _ 2 [2, 2, 19, 31, 5849, 18047]
  · simp only [List.forall_mem_cons, p5849, p18047]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p327757380757 : Nat.Prime 327757380757 := by
  apply certified _ 14 [2, 2, 3, 13, 37, 56784023]
  · simp only [List.forall_mem_cons, p56784023]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p528124563007 : Nat.Prime 528124563007 := by
  apply certified _ 5 [2, 3, 23, 31, 37, 89, 37489]
  · simp only [List.forall_mem_cons, p37489]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p582536588861 : Nat.Prime 582536588861 := by
  apply certified _ 2 [2, 2, 5, 617, 1787, 26417]
  · simp only [List.forall_mem_cons, p26417]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p804992177299 : Nat.Prime 804992177299 := by
  apply certified _ 2 [2, 3, 47, 2854582189]
  · simp only [List.forall_mem_cons, p2854582189]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2653541220611 : Nat.Prime 2653541220611 := by
  apply certified _ 2 [2, 5, 7, 37907731723]
  · simp only [List.forall_mem_cons, p37907731723]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p3339337037807 : Nat.Prime 3339337037807 := by
  apply certified _ 5 [2, 7, 11, 131, 10301, 16069]
  · simp only [List.forall_mem_cons, p16069, p10301]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p3495219533167 : Nat.Prime 3495219533167 := by
  apply certified _ 5 [2, 3, 582536588861]
  · simp only [List.forall_mem_cons, p582536588861]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5357493895483 : Nat.Prime 5357493895483 := by
  apply certified _ 3 [2, 3, 3, 116959, 2544811]
  · simp only [List.forall_mem_cons, p116959, p2544811]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p9052516320917 : Nat.Prime 9052516320917 := by
  apply certified _ 2 [2, 2, 29, 37, 2109160373]
  · simp only [List.forall_mem_cons, p2109160373]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p14134419850597 : Nat.Prime 14134419850597 := by
  apply certified _ 2 [2, 2, 3, 101, 23671, 492673]
  · simp only [List.forall_mem_cons, p23671, p492673]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p15427219380457 : Nat.Prime 15427219380457 := by
  apply certified _ 7 [2, 2, 2, 3, 13, 17, 53, 59, 930157]
  · simp only [List.forall_mem_cons, p930157]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p69955944598277 : Nat.Prime 69955944598277 := by
  apply certified _ 2 [2, 2, 11, 233, 6823638763]
  · simp only [List.forall_mem_cons, p6823638763]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p544896287951143 : Nat.Prime 544896287951143 := by
  apply certified _ 3 [2, 3, 41, 53, 131, 13309, 23971]
  · simp only [List.forall_mem_cons, p23971, p13309]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p631331429277859 : Nat.Prime 631331429277859 := by
  apply certified _ 2 [2, 3, 271, 359, 1081539587]
  · simp only [List.forall_mem_cons, p1081539587]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1165527773351003 : Nat.Prime 1165527773351003 := by
  apply certified _ 2 [2, 643, 4937, 183577111]
  · simp only [List.forall_mem_cons, p183577111]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2575135369222133 : Nat.Prime 2575135369222133 := by
  apply certified _ 2 [2, 2, 23, 53, 528124563007]
  · simp only [List.forall_mem_cons, p528124563007]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p3585642171096043 : Nat.Prime 3585642171096043 := by
  apply certified _ 3 [2, 3, 3, 3, 3, 89, 248692063469]
  · simp only [List.forall_mem_cons, p248692063469]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p4859376605767591 : Nat.Prime 4859376605767591 := by
  apply certified _ 12 [2, 3, 5, 29, 92269, 60534853]
  · simp only [List.forall_mem_cons, p92269, p60534853]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6065932345248247 : Nat.Prime 6065932345248247 := by
  apply certified _ 3 [2, 3, 21651121, 46694521]
  · simp only [List.forall_mem_cons, p21651121, p46694521]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6708178025567341 : Nat.Prime 6708178025567341 := by
  apply certified _ 6 [2, 2, 3, 5, 7, 167, 2521, 37937261]
  · simp only [List.forall_mem_cons, p37937261]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p21437605762796233 : Nat.Prime 21437605762796233 := by
  apply certified _ 5 [2, 2, 2, 3, 3, 29, 47, 218447926987]
  · simp only [List.forall_mem_cons, p218447926987]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p27598490420822947 : Nat.Prime 27598490420822947 := by
  apply certified _ 2 [2, 3, 3, 19, 337969, 238771427]
  · simp only [List.forall_mem_cons, p337969, p238771427]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p36336800512160839 : Nat.Prime 36336800512160839 := by
  apply certified _ 3 [2, 3, 3, 223, 9052516320917]
  · simp only [List.forall_mem_cons, p9052516320917]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p58312519269211093 : Nat.Prime 58312519269211093 := by
  apply certified _ 2 [2, 2, 3, 4859376605767591]
  · simp only [List.forall_mem_cons, p4859376605767591]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p106906181114016397 : Nat.Prime 106906181114016397 := by
  apply certified _ 22 [2, 2, 3, 3, 7, 17, 31, 804992177299]
  · simp only [List.forall_mem_cons, p804992177299]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p118505370149481239 : Nat.Prime 118505370149481239 := by
  apply certified _ 11 [2, 7, 11, 11, 69955944598277]
  · simp only [List.forall_mem_cons, p69955944598277]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p178448335245923551 : Nat.Prime 178448335245923551 := by
  apply certified _ 6 [2, 3, 5, 5, 73553, 16174127069]
  · simp only [List.forall_mem_cons, p73553, p16174127069]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1039454884912343621 : Nat.Prime 1039454884912343621 := by
  apply certified _ 2 [2, 2, 5, 7, 127, 8951, 49019, 133241]
  · simp only [List.forall_mem_cons, p8951, p49019, p133241]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1863545304792909061 : Nat.Prime 1863545304792909061 := by
  apply certified _ 6 [2, 2, 3, 3, 5, 19, 544896287951143]
  · simp only [List.forall_mem_cons, p544896287951143]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5022872233605666871 : Nat.Prime 5022872233605666871 := by
  apply certified _ 3 [2, 3, 5, 1093, 5557, 27565782029]
  · simp only [List.forall_mem_cons, p5557, p27565782029]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p14648913693107146357 : Nat.Prime 14648913693107146357 := by
  apply certified _ 2 [2, 2, 3, 61, 60703897, 329668739]
  · simp only [List.forall_mem_cons, p329668739, p60703897]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p299051868215083704971 : Nat.Prime 299051868215083704971 := by
  apply certified _ 6 [2, 5, 823, 36336800512160839]
  · simp only [List.forall_mem_cons, p36336800512160839]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p353729277480602391317 : Nat.Prime 353729277480602391317 := by
  apply certified _ 2 [2, 2, 13, 601, 1831, 63617, 97169879]
  · simp only [List.forall_mem_cons, p63617, p97169879]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p614789822365154359909 : Nat.Prime 614789822365154359909 := by
  apply certified _ 6 [2, 2, 3, 101, 439, 7027, 164433225403]
  · simp only [List.forall_mem_cons, p7027, p164433225403]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p974736250413007345943 : Nat.Prime 974736250413007345943 := by
  apply certified _ 7 [2, 7, 577, 8537, 14134419850597]
  · simp only [List.forall_mem_cons, p8537, p14134419850597]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1975395304598545436017 : Nat.Prime 1975395304598545436017 := by
  apply certified _ 10 [2, 2, 2, 2, 3, 440239, 2161759, 43243117]
  · simp only [List.forall_mem_cons, p440239, p43243117, p2161759]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p4440908034265130232169 : Nat.Prime 4440908034265130232169 := by
  apply certified _ 11 [2, 2, 2, 3, 7, 13, 137, 74761, 198528781261]
  · simp only [List.forall_mem_cons, p74761, p198528781261]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p55993568495231890452157 : Nat.Prime 55993568495231890452157 := by
  apply certified _ 2 [2, 2, 3, 217661, 21437605762796233]
  · simp only [List.forall_mem_cons, p217661, p21437605762796233]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1310045520555081872947393 : Nat.Prime 1310045520555081872947393 := by
  apply certified _ 10 [2, 2, 2, 2, 2, 2, 3, 7, 974736250413007345943]
  · simp only [List.forall_mem_cons, p974736250413007345943]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p1339318016517813805619527 : Nat.Prime 1339318016517813805619527 := by
  apply certified _ 5 [2, 3, 113, 1975395304598545436017]
  · simp only [List.forall_mem_cons, p1975395304598545436017]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p5160441010808557806518429 : Nat.Prime 5160441010808557806518429 := by
  apply certified _ 3 [2, 2, 11, 29, 34127, 118505370149481239]
  · simp only [List.forall_mem_cons, p34127, p118505370149481239]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p14731071218372842851056069 : Nat.Prime 14731071218372842851056069 := by
  apply certified _ 2 [2, 2, 169199, 4062701, 5357493895483]
  · simp only [List.forall_mem_cons, p169199, p4062701, p5357493895483]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p72246174151319809291258007 : Nat.Prime 72246174151319809291258007 := by
  apply certified _ 5 [2, 7, 5160441010808557806518429]
  · simp only [List.forall_mem_cons, p5160441010808557806518429]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p81467999847607904321136377 : Nat.Prime 81467999847607904321136377 := by
  apply certified _ 3 [2, 2, 2, 695171, 14648913693107146357]
  · simp only [List.forall_mem_cons, p695171, p14648913693107146357]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p553143617296955601932204753 : Nat.Prime 553143617296955601932204753 := by
  apply certified _ 3 [2, 2, 2, 2, 53, 1061, 614789822365154359909]
  · simp only [List.forall_mem_cons, p614789822365154359909]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6053413019594444547884628917 : Nat.Prime 6053413019594444547884628917 := by
  apply certified _ 2 [2, 2, 311, 2611199, 1863545304792909061]
  · simp only [List.forall_mem_cons, p2611199, p1863545304792909061]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p148303579333636000036955565587 : Nat.Prime 148303579333636000036955565587 := by
  apply certified _ 2 [2, 247956283, 299051868215083704971]
  · simp only [List.forall_mem_cons, p247956283, p299051868215083704971]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p232921665463855065155015814569 : Nat.Prime 232921665463855065155015814569 := by
  apply certified _ 3 [2, 2, 2, 13, 31, 72246174151319809291258007]
  · simp only [List.forall_mem_cons, p72246174151319809291258007]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p90778245483882153483569567724259 : Nat.Prime 90778245483882153483569567724259 := by
  apply certified _ 3 [2, 3, 7, 13, 37337, 59791, 3262224011, 22829695829]
  · simp only [List.forall_mem_cons, p37337, p59791, p3262224011, p22829695829]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p265457494880237509401972762941993 : Nat.Prime 265457494880237509401972762941993 := by
  apply certified _ 3 [2, 2, 2, 5023, 18675439, 353729277480602391317]
  · simp only [List.forall_mem_cons, p5023, p18675439, p353729277480602391317]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p19386837104810232468830979355794989 : Nat.Prime 19386837104810232468830979355794989 := by
  apply certified _ 2 [2, 2, 11, 2971, 148303579333636000036955565587]
  · simp only [List.forall_mem_cons, p148303579333636000036955565587]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p282789059470568586463609095534188131 : Nat.Prime 282789059470568586463609095534188131 := by
  apply certified _ 15 [2, 3, 5, 7, 11, 31, 37, 102678983629, 1039454884912343621]
  · simp only [List.forall_mem_cons, p102678983629, p1039454884912343621]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p23567721955657194776649723510218140673 : Nat.Prime 23567721955657194776649723510218140673 := by
  apply certified _ 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 937, 2729, 3495219533167, 2575135369222133]
  · simp only [List.forall_mem_cons, p3495219533167, p2575135369222133]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p410716897908682995496769866714903337573 : Nat.Prime 410716897908682995496769866714903337573 := by
  apply certified _ 2 [2, 2, 17, 61, 373, 265457494880237509401972762941993]
  · simp only [List.forall_mem_cons, p265457494880237509401972762941993]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p31260942106937851086988820434353782113597 : Nat.Prime 31260942106937851086988820434353782113597 := by
  apply certified _ 2 [2, 2, 3, 3, 7, 5182379, 5390146523, 4440908034265130232169]
  · simp only [List.forall_mem_cons, p5182379, p5390146523, p4440908034265130232169]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p2567189623092244449323981439041677545536149 : Nat.Prime 2567189623092244449323981439041677545536149 := by
  apply certified _ 2 [2, 2, 3, 13, 58193, 282789059470568586463609095534188131]
  · simp only [List.forall_mem_cons, p58193, p282789059470568586463609095534188131]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p8373094558265845827516770230329627536146799 : Nat.Prime 8373094558265845827516770230329627536146799 := by
  apply certified _ 7 [2, 5839, 47809, 11197579487, 1339318016517813805619527]
  · simp only [List.forall_mem_cons, p5839, p47809, p11197579487, p1339318016517813805619527]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p165337136995061861490728657086431249608356451 : Nat.Prime 165337136995061861490728657086431249608356451 := by
  apply certified _ 2 [2, 5, 5, 79, 461096189, 90778245483882153483569567724259]
  · simp only [List.forall_mem_cons, p461096189, p90778245483882153483569567724259]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p334130122469124376448502703576854973706716799 : Nat.Prime 334130122469124376448502703576854973706716799 := by
  apply certified _ 17 [2, 27598490420822947, 6053413019594444547884628917]
  · simp only [List.forall_mem_cons, p27598490420822947, p6053413019594444547884628917]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p472362132581542660756039516449996870043763098571 : Nat.Prime 472362132581542660756039516449996870043763098571 := by
  apply certified _ 2 [2, 5, 2309, 4676323, 3339337037807, 1310045520555081872947393]
  · simp only [List.forall_mem_cons, p4676323, p3339337037807, p1310045520555081872947393]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p166537906346951949512555048980432872272371711730863 : Nat.Prime 166537906346951949512555048980432872272371711730863 := by
  apply certified _ 5 [2, 3, 47, 53, 139, 6917, 12882676069, 15427219380457, 58312519269211093]
  · simp only [List.forall_mem_cons, p6917, p12882676069, p15427219380457, p58312519269211093]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p7605097443758365136139127684454071607399120106122204869 : Nat.Prime 7605097443758365136139127684454071607399120106122204869 := by
  apply certified _ 11 [2, 2, 3, 7, 4931, 7152083, 2567189623092244449323981439041677545536149]
  · simp only [List.forall_mem_cons, p7152083, p2567189623092244449323981439041677545536149]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p172065054976772107675581285529480503164616022973170886021 : Nat.Prime 172065054976772107675581285529480503164616022973170886021 := by
  apply certified _ 2 [2, 2, 5, 7, 146783975557, 8373094558265845827516770230329627536146799]
  · simp only [List.forall_mem_cons, p146783975557, p8373094558265845827516770230329627536146799]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p297944641350014385275436610378443430138886610872100450151 : Nat.Prime 297944641350014385275436610378443430138886610872100450151 := by
  apply certified _ 21 [2, 3, 5, 5, 11927, 166537906346951949512555048980432872272371711730863]
  · simp only [List.forall_mem_cons, p11927, p166537906346951949512555048980432872272371711730863]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p273555355051988393946924422809812955718146350217215709137931 : Nat.Prime 273555355051988393946924422809812955718146350217215709137931 := by
  apply certified _ 3 [2, 3, 5, 11, 109, 7605097443758365136139127684454071607399120106122204869]
  · simp only [List.forall_mem_cons, p7605097443758365136139127684454071607399120106122204869]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p40687297931583212434454439521483153605327032354191178561100493 : Nat.Prime 40687297931583212434454439521483153605327032354191178561100493 := by
  apply certified _ 2 [2, 2, 4037183, 106906181114016397, 23567721955657194776649723510218140673]
  · simp only [List.forall_mem_cons, p4037183, p106906181114016397, p23567721955657194776649723510218140673]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p6297297448939257420492825692420433831955731153612194642748437393 : Nat.Prime 6297297448939257420492825692420433831955731153612194642748437393 := by
  apply certified _ 5 [2, 2, 2, 2, 7, 31, 83, 127, 172065054976772107675581285529480503164616022973170886021]
  · simp only [List.forall_mem_cons, p172065054976772107675581285529480503164616022973170886021]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p30463286638653519166134094991866993173323371437334932151335007280987 : Nat.Prime 30463286638653519166134094991866993173323371437334932151335007280987 := by
  apply certified _ 2 [2, 691, 7057, 2380463, 31569287, 178448335245923551, 232921665463855065155015814569]
  · simp only [List.forall_mem_cons, p7057, p2380463, p31569287, p178448335245923551, p232921665463855065155015814569]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p61471288489178400502227511463990027154771532183167217954139642300211427949197 : Nat.Prime 61471288489178400502227511463990027154771532183167217954139642300211427949197 := by
  apply certified _ 2 [2, 2, 3, 3, 3, 3, 569, 26360903, 1625900707, 47053325621, 165337136995061861490728657086431249608356451]
  · simp only [List.forall_mem_cons, p26360903, p1625900707, p47053325621, p165337136995061861490728657086431249608356451]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p446092199703710200243488189611814726284358184224501445344992905869145850914339049 : Nat.Prime 446092199703710200243488189611814726284358184224501445344992905869145850914339049 := by
  apply certified _ 3 [2, 2, 2, 19, 653, 2653541220611, 3585642171096043, 472362132581542660756039516449996870043763098571]
  · simp only [List.forall_mem_cons, p2653541220611, p3585642171096043, p472362132581542660756039516449996870043763098571]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 := by
  apply certified _ 3 [2, 3, 11, 409, 9011, 9829, 6708178025567341, 6297297448939257420492825692420433831955731153612194642748437393]
  · simp only [List.forall_mem_cons, p9011, p9829, p6708178025567341, p6297297448939257420492825692420433831955731153612194642748437393]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 := by
  apply certified _ 7 [2, 2, 2, 3, 17, 1567, 14731071218372842851056069, 553143617296955601932204753, 19386837104810232468830979355794989]
  · simp only [List.forall_mem_cons, p14731071218372842851056069, p553143617296955601932204753, p19386837104810232468830979355794989]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 := by
  apply certified _ 2 [2, 3, 3, 929, 248827, 81467999847607904321136377, 297944641350014385275436610378443430138886610872100450151]
  · simp only [List.forall_mem_cons, p248827, p81467999847607904321136377, p297944641350014385275436610378443430138886610872100450151]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 := by
  apply certified _ 2 [2, 2, 3, 31, 991, 1110031619, 6065932345248247, 40687297931583212434454439521483153605327032354191178561100493]
  · simp only [List.forall_mem_cons, p1110031619, p6065932345248247, p40687297931583212434454439521483153605327032354191178561100493]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 := by
  apply certified _ 3 [2, 3, 23, 4783, 5022872233605666871, 30463286638653519166134094991866993173323371437334932151335007280987]
  · simp only [List.forall_mem_cons, p5022872233605666871, p30463286638653519166134094991866993173323371437334932151335007280987]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 := by
  apply certified _ 7 [2, 2, 2, 2, 3, 3, 3, 97, 157351, 55993568495231890452157, 273555355051988393946924422809812955718146350217215709137931]
  · simp only [List.forall_mem_cons, p157351, p55993568495231890452157, p273555355051988393946924422809812955718146350217215709137931]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 := by
  apply certified _ 3 [2, 3, 13, 4975823, 1058408119, 631331429277859, 1165527773351003, 334130122469124376448502703576854973706716799]
  · simp only [List.forall_mem_cons, p4975823, p1058408119, p631331429277859, p1165527773351003, p334130122469124376448502703576854973706716799]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 := by
  apply certified _ 7 [2, 2, 3, 59, 319779389, 446092199703710200243488189611814726284358184224501445344992905869145850914339049]
  · simp only [List.forall_mem_cons, p319779389, p446092199703710200243488189611814726284358184224501445344992905869145850914339049]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 := by
  apply certified _ 3 [2, 3, 3, 199, 475141, 965357, 61471288489178400502227511463990027154771532183167217954139642300211427949197]
  · simp only [List.forall_mem_cons, p475141, p965357, p61471288489178400502227511463990027154771532183167217954139642300211427949197]
    decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
private theorem p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 := by
  apply certified _ 7 [2, 2, 2, 3, 327757380757, 410716897908682995496769866714903337573, 31260942106937851086988820434353782113597]
  · simp only [List.forall_mem_cons, p327757380757, p410716897908682995496769866714903337573, p31260942106937851086988820434353782113597]
    decide +kernel
  · decide +kernel

-- Toplic's progression starts here and has common difference 210.
private def base : ℕ :=
  100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719

private theorem terms_prime : ∀ i < 10, Nat.Prime (base + i*210) := by
  intro i hi
  interval_cases i
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399
  · exact p100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609

-- Try small divisors first, then a base-two Fermat test for the remaining gaps.
private def divisorWitness (n : ℕ) : ℕ :=
  ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
    41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293].find? (fun d => n % d == 0)).getD 1

private def gapOK (n : ℕ) : Bool :=
  let d := divisorWitness n
  decide (1 < d ∧ d < n ∧ n % d = 0) ||
    decide (n < 64^52 ∧ residue n 52 2 n % n ≠ 2 % n)

private theorem gapOK_composite (n : ℕ) (h : gapOK n = true) : ¬ n.Prime := by
  apply composite n (divisorWitness n)
  simpa only [gapOK, Bool.or_eq_true, decide_eq_true_eq] using h

private def gapBlock (i : ℕ) : Bool :=
  (List.range 209).all fun j => gapOK (base + i*210+j+1)

set_option maxRecDepth 4096 in
private theorem gap0 : gapBlock 0 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap1 : gapBlock 1 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap2 : gapBlock 2 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap3 : gapBlock 3 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap4 : gapBlock 4 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap5 : gapBlock 5 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap6 : gapBlock 6 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap7 : gapBlock 7 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem gap8 : gapBlock 8 = true := by decide +kernel

private theorem gaps_composite (i : ℕ) (hi : i < 9) (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (base+i*210+j+1) := by
  have ok : gapBlock i = true := by
    interval_cases i
    · exact gap0
    · exact gap1
    · exact gap2
    · exact gap3
    · exact gap4
    · exact gap5
    · exact gap6
    · exact gap7
    · exact gap8
  change (List.range 209).all (fun t => gapOK (base+i*210+t+1)) = true at ok
  exact gapOK_composite _ (List.all_eq_true.mp ok j (List.mem_range.mpr hj))


private theorem progression_of_certificates (b : ℕ)
    (primes : ∀ i < 10, Nat.Prime (b + i*210))
    (gaps : ∀ i < 9, ∀ j < 209, ¬ Nat.Prime (b + i*210 + j+1)) :
    ∀ k ≥ 3, k ≤ 10 → ∃ s : Set ℕ, Erdos141.Set.IsAPAndPrimeProgressionOfLength s k := by
  let start := Nat.count Nat.Prime b
  have indices : ∀ i < 10, Nat.nth Nat.Prime (start+i) = b+i*210 := by
    intro i
    induction i with
    | zero => simpa [start] using Nat.nth_count (primes 0 (by decide) : Nat.Prime (b+0*210))
    | succ i ih =>
      intro hi
      have prev := ih (by omega)
      let next := Nat.nth Nat.Prime (start+i+1)
      have hlt : b+i*210 < next := by
        rw [← prev]
        exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self _)
      have hle : next ≤ b+(i+1)*210 := by
        by_contra! hc
        have := Nat.le_nth_of_lt_nth_succ hc (primes (i+1) hi)
        omega
      have heq : next = b+(i+1)*210 := by
        by_contra h
        let j := next - (b+i*210+1)
        have hj : j < 209 := by dsimp [j]; omega
        have hval : b+i*210+j+1 = next := by dsimp [j]; omega
        exact gaps i (by omega) j hj (hval ▸ Nat.prime_nth_prime _)
      exact heq
  intro k _ hk
  let term (i : Fin k) := b + i.val*210
  have hinj : Function.Injective term := by
    intro i j h
    apply Fin.ext
    dsimp [term] at h
    omega
  have hcard : ENat.card (Set.range term) = k := by
    rw [← ENat.card_congr (Equiv.ofInjective term hinj)]
    simp
  refine ⟨Set.range term, ⟨b, 210, hcard, ?_⟩, start, hcard, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, by simp [term]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by exact_mod_cast hi⟩, by simp [term]⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, indices _ (by omega)⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' : i < k := by exact_mod_cast hi
      exact ⟨⟨i,hi'⟩, (indices _ (by omega)).symm⟩


end ConsecutivePrimes141

theorem OMA.solution : OMA.R_Erdos141_erdos_141_R1.H1 := by
  unfold OMA.R_Erdos141_erdos_141_R1.H1
  intro k hk hk'
  exact ConsecutivePrimes141.progression_of_certificates _
    ConsecutivePrimes141.terms_prime ConsecutivePrimes141.gaps_composite k (by omega) hk'
