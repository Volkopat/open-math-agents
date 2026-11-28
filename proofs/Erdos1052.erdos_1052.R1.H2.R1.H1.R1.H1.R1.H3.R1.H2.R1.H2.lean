import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1

-- Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H2.R1.H2: hypothesis H2 of reduction
-- Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H2.R1 (3 the only repeated odd prime, exponent of 3
-- equal to 499).
-- Credit: @adammcarter
--
-- Proof: the case is impossible, so H2 holds with any bound.  Every odd prime of 3^499 + 1 is a
-- simple prime of n with source 3^499 + 1, and the odd primes of p + 1 for a simple prime p are again
-- simple primes.  Starting from the 113-digit prime factor of 3^499 + 1, the chain recorded in
-- kill3_e499 ends in the square of a prime dividing some p + 1, which the balance equation
-- (2^a + 1)(3^e + 1) prod (p + 1) = 2^(a+1) 3^e prod p forbids.  Witness primes above 4.3 * 10^7 are
-- certified by the Lucas test (p - 1 factorizations from factordb, ECM and PARI, re-checked here).

namespace OMA.Erdos1052E499

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1 hiding H1 H2 main

theorem prime_381807514177 : Nat.Prime 381807514177 := by
  refine lucas_primality 381807514177 (5 : ZMod 381807514177) ?_ (fun q hq hd => ?_)
  · rw [show 381807514177 - 1 = 381807514176 from by norm_num]
    reduce_mod_char
  · have e : 381807514177 - 1 = [2 ^ 6, 3 ^ 1, 11 ^ 1, 743 ^ 1, 243311 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381807514177 - 1) / 2 = 190903757088 from by norm_num]
      have h2 : (5 : ZMod 381807514177) ^ 190903757088 = ((381807514176 : ℕ) : ZMod 381807514177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381807514177 - 1) / 3 = 127269171392 from by norm_num]
      have h2 : (5 : ZMod 381807514177) ^ 127269171392 = ((2254679824 : ℕ) : ZMod 381807514177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381807514177 - 1) / 11 = 34709774016 from by norm_num]
      have h2 : (5 : ZMod 381807514177) ^ 34709774016 = ((314096226083 : ℕ) : ZMod 381807514177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381807514177 - 1) / 743 = 513872832 from by norm_num]
      have h2 : (5 : ZMod 381807514177) ^ 513872832 = ((111715611347 : ℕ) : ZMod 381807514177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (381807514177 - 1) / 243311 = 1569216 from by norm_num]
      have h2 : (5 : ZMod 381807514177) ^ 1569216 = ((80296562244 : ℕ) : ZMod 381807514177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_205006741598811803341 : Nat.Prime 205006741598811803341 := by
  refine lucas_primality 205006741598811803341 (6 : ZMod 205006741598811803341) ?_ (fun q hq hd => ?_)
  · rw [show 205006741598811803341 - 1 = 205006741598811803340 from by norm_num]
    reduce_mod_char
  · have e : 205006741598811803341 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 8948957 ^ 1, 381807514177 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205006741598811803341 - 1) / 2 = 102503370799405901670 from by norm_num]
      have h2 : (6 : ZMod 205006741598811803341) ^ 102503370799405901670 = ((205006741598811803340 : ℕ) : ZMod 205006741598811803341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205006741598811803341 - 1) / 3 = 68335580532937267780 from by norm_num]
      have h2 : (6 : ZMod 205006741598811803341) ^ 68335580532937267780 = ((120240024007108816426 : ℕ) : ZMod 205006741598811803341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205006741598811803341 - 1) / 5 = 41001348319762360668 from by norm_num]
      have h2 : (6 : ZMod 205006741598811803341) ^ 41001348319762360668 = ((155993987234533426390 : ℕ) : ZMod 205006741598811803341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205006741598811803341 - 1) / 8948957 = 22908450850620 from by norm_num]
      have h2 : (6 : ZMod 205006741598811803341) ^ 22908450850620 = ((178004175476616089562 : ℕ) : ZMod 205006741598811803341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_381807514177).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (205006741598811803341 - 1) / 381807514177 = 536937420 from by norm_num]
      have h2 : (6 : ZMod 205006741598811803341) ^ 536937420 = ((102866371784601936637 : ℕ) : ZMod 205006741598811803341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_368438138049559 : Nat.Prime 368438138049559 := by
  refine lucas_primality 368438138049559 (3 : ZMod 368438138049559) ?_ (fun q hq hd => ?_)
  · rw [show 368438138049559 - 1 = 368438138049558 from by norm_num]
    reduce_mod_char
  · have e : 368438138049559 - 1 = [2 ^ 1, 3 ^ 1, 17 ^ 1, 223621 ^ 1, 16152949 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368438138049559 - 1) / 2 = 184219069024779 from by norm_num]
      have h2 : (3 : ZMod 368438138049559) ^ 184219069024779 = ((368438138049558 : ℕ) : ZMod 368438138049559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368438138049559 - 1) / 3 = 122812712683186 from by norm_num]
      have h2 : (3 : ZMod 368438138049559) ^ 122812712683186 = ((238527280926815 : ℕ) : ZMod 368438138049559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368438138049559 - 1) / 17 = 21672831649974 from by norm_num]
      have h2 : (3 : ZMod 368438138049559) ^ 21672831649974 = ((296074808195971 : ℕ) : ZMod 368438138049559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368438138049559 - 1) / 223621 = 1647600798 from by norm_num]
      have h2 : (3 : ZMod 368438138049559) ^ 1647600798 = ((244524232145907 : ℕ) : ZMod 368438138049559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368438138049559 - 1) / 16152949 = 22809342 from by norm_num]
      have h2 : (3 : ZMod 368438138049559) ^ 22809342 = ((288281800777878 : ℕ) : ZMod 368438138049559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_784773234045560671 : Nat.Prime 784773234045560671 := by
  refine lucas_primality 784773234045560671 (6 : ZMod 784773234045560671) ?_ (fun q hq hd => ?_)
  · rw [show 784773234045560671 - 1 = 784773234045560670 from by norm_num]
    reduce_mod_char
  · have e : 784773234045560671 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 71 ^ 1, 368438138049559 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784773234045560671 - 1) / 2 = 392386617022780335 from by norm_num]
      have h2 : (6 : ZMod 784773234045560671) ^ 392386617022780335 = ((784773234045560670 : ℕ) : ZMod 784773234045560671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784773234045560671 - 1) / 3 = 261591078015186890 from by norm_num]
      have h2 : (6 : ZMod 784773234045560671) ^ 261591078015186890 = ((677666720900376353 : ℕ) : ZMod 784773234045560671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784773234045560671 - 1) / 5 = 156954646809112134 from by norm_num]
      have h2 : (6 : ZMod 784773234045560671) ^ 156954646809112134 = ((492464754512384220 : ℕ) : ZMod 784773234045560671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784773234045560671 - 1) / 71 = 11053144141486770 from by norm_num]
      have h2 : (6 : ZMod 784773234045560671) ^ 11053144141486770 = ((573390621574702050 : ℕ) : ZMod 784773234045560671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_368438138049559).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (784773234045560671 - 1) / 368438138049559 = 2130 from by norm_num]
      have h2 : (6 : ZMod 784773234045560671) ^ 2130 = ((362419266908184520 : ℕ) : ZMod 784773234045560671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_165849617 : Nat.Prime 165849617 := by
  refine lucas_primality 165849617 (3 : ZMod 165849617) ?_ (fun q hq hd => ?_)
  · rw [show 165849617 - 1 = 165849616 from by norm_num]
    reduce_mod_char
  · have e : 165849617 - 1 = [2 ^ 4, 757 ^ 1, 13693 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165849617 - 1) / 2 = 82924808 from by norm_num]
      have h2 : (3 : ZMod 165849617) ^ 82924808 = ((165849616 : ℕ) : ZMod 165849617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165849617 - 1) / 757 = 219088 from by norm_num]
      have h2 : (3 : ZMod 165849617) ^ 219088 = ((29012949 : ℕ) : ZMod 165849617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165849617 - 1) / 13693 = 12112 from by norm_num]
      have h2 : (3 : ZMod 165849617) ^ 12112 = ((37678404 : ℕ) : ZMod 165849617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1822160764176306369698582099 : Nat.Prime 1822160764176306369698582099 := by
  refine lucas_primality 1822160764176306369698582099 (2 : ZMod 1822160764176306369698582099) ?_ (fun q hq hd => ?_)
  · rw [show 1822160764176306369698582099 - 1 = 1822160764176306369698582098 from by norm_num]
    reduce_mod_char
  · have e : 1822160764176306369698582099 - 1 = [2 ^ 1, 7 ^ 1, 165849617 ^ 1, 784773234045560671 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1822160764176306369698582099 - 1) / 2 = 911080382088153184849291049 from by norm_num]
      have h2 : (2 : ZMod 1822160764176306369698582099) ^ 911080382088153184849291049 = ((1822160764176306369698582098 : ℕ) : ZMod 1822160764176306369698582099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1822160764176306369698582099 - 1) / 7 = 260308680596615195671226014 from by norm_num]
      have h2 : (2 : ZMod 1822160764176306369698582099) ^ 260308680596615195671226014 = ((347953456275146664624417452 : ℕ) : ZMod 1822160764176306369698582099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_165849617).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1822160764176306369698582099 - 1) / 165849617 = 10986825276637849394 from by norm_num]
      have h2 : (2 : ZMod 1822160764176306369698582099) ^ 10986825276637849394 = ((36589058139541607894383273 : ℕ) : ZMod 1822160764176306369698582099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_784773234045560671).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1822160764176306369698582099 - 1) / 784773234045560671 = 2321894638 from by norm_num]
      have h2 : (2 : ZMod 1822160764176306369698582099) ^ 2321894638 = ((382485111684585329798808850 : ℕ) : ZMod 1822160764176306369698582099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_269837977 : Nat.Prime 269837977 := by
  refine lucas_primality 269837977 (7 : ZMod 269837977) ?_ (fun q hq hd => ?_)
  · rw [show 269837977 - 1 = 269837976 from by norm_num]
    reduce_mod_char
  · have e : 269837977 - 1 = [2 ^ 3, 3 ^ 1, 2129 ^ 1, 5281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269837977 - 1) / 2 = 134918988 from by norm_num]
      have h2 : (7 : ZMod 269837977) ^ 134918988 = ((269837976 : ℕ) : ZMod 269837977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269837977 - 1) / 3 = 89945992 from by norm_num]
      have h2 : (7 : ZMod 269837977) ^ 89945992 = ((170304653 : ℕ) : ZMod 269837977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269837977 - 1) / 2129 = 126744 from by norm_num]
      have h2 : (7 : ZMod 269837977) ^ 126744 = ((38559417 : ℕ) : ZMod 269837977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (269837977 - 1) / 5281 = 51096 from by norm_num]
      have h2 : (7 : ZMod 269837977) ^ 51096 = ((58587895 : ℕ) : ZMod 269837977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9992082479003519 : Nat.Prime 9992082479003519 := by
  refine lucas_primality 9992082479003519 (11 : ZMod 9992082479003519) ?_ (fun q hq hd => ?_)
  · rw [show 9992082479003519 - 1 = 9992082479003518 from by norm_num]
    reduce_mod_char
  · have e : 9992082479003519 - 1 = [2 ^ 1, 31 ^ 1, 53 ^ 1, 59 ^ 1, 191 ^ 1, 269837977 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9992082479003519 - 1) / 2 = 4996041239501759 from by norm_num]
      have h2 : (11 : ZMod 9992082479003519) ^ 4996041239501759 = ((9992082479003518 : ℕ) : ZMod 9992082479003519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9992082479003519 - 1) / 31 = 322325241258178 from by norm_num]
      have h2 : (11 : ZMod 9992082479003519) ^ 322325241258178 = ((4949996997882853 : ℕ) : ZMod 9992082479003519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9992082479003519 - 1) / 53 = 188529858094406 from by norm_num]
      have h2 : (11 : ZMod 9992082479003519) ^ 188529858094406 = ((7678372509428475 : ℕ) : ZMod 9992082479003519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9992082479003519 - 1) / 59 = 169357330152602 from by norm_num]
      have h2 : (11 : ZMod 9992082479003519) ^ 169357330152602 = ((1931175853234163 : ℕ) : ZMod 9992082479003519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9992082479003519 - 1) / 191 = 52314567952898 from by norm_num]
      have h2 : (11 : ZMod 9992082479003519) ^ 52314567952898 = ((2905204505341499 : ℕ) : ZMod 9992082479003519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_269837977).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9992082479003519 - 1) / 269837977 = 37029934 from by norm_num]
      have h2 : (11 : ZMod 9992082479003519) ^ 37029934 = ((631160505598206 : ℕ) : ZMod 9992082479003519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_139889154706049267 : Nat.Prime 139889154706049267 := by
  refine lucas_primality 139889154706049267 (2 : ZMod 139889154706049267) ?_ (fun q hq hd => ?_)
  · rw [show 139889154706049267 - 1 = 139889154706049266 from by norm_num]
    reduce_mod_char
  · have e : 139889154706049267 - 1 = [2 ^ 1, 7 ^ 1, 9992082479003519 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (139889154706049267 - 1) / 2 = 69944577353024633 from by norm_num]
      have h2 : (2 : ZMod 139889154706049267) ^ 69944577353024633 = ((139889154706049266 : ℕ) : ZMod 139889154706049267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (139889154706049267 - 1) / 7 = 19984164958007038 from by norm_num]
      have h2 : (2 : ZMod 139889154706049267) ^ 19984164958007038 = ((139734385284806513 : ℕ) : ZMod 139889154706049267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9992082479003519).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (139889154706049267 - 1) / 9992082479003519 = 14 from by norm_num]
      have h2 : (2 : ZMod 139889154706049267) ^ 14 = ((16384 : ℕ) : ZMod 139889154706049267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_91051843 : Nat.Prime 91051843 := by
  refine lucas_primality 91051843 (2 : ZMod 91051843) ?_ (fun q hq hd => ?_)
  · rw [show 91051843 - 1 = 91051842 from by norm_num]
    reduce_mod_char
  · have e : 91051843 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 109 ^ 1, 19889 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91051843 - 1) / 2 = 45525921 from by norm_num]
      have h2 : (2 : ZMod 91051843) ^ 45525921 = ((91051842 : ℕ) : ZMod 91051843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91051843 - 1) / 3 = 30350614 from by norm_num]
      have h2 : (2 : ZMod 91051843) ^ 30350614 = ((65009665 : ℕ) : ZMod 91051843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91051843 - 1) / 7 = 13007406 from by norm_num]
      have h2 : (2 : ZMod 91051843) ^ 13007406 = ((18995599 : ℕ) : ZMod 91051843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91051843 - 1) / 109 = 835338 from by norm_num]
      have h2 : (2 : ZMod 91051843) ^ 835338 = ((69126165 : ℕ) : ZMod 91051843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91051843 - 1) / 19889 = 4578 from by norm_num]
      have h2 : (2 : ZMod 91051843) ^ 4578 = ((45515321 : ℕ) : ZMod 91051843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_318317243129 : Nat.Prime 318317243129 := by
  refine lucas_primality 318317243129 (3 : ZMod 318317243129) ?_ (fun q hq hd => ?_)
  · rw [show 318317243129 - 1 = 318317243128 from by norm_num]
    reduce_mod_char
  · have e : 318317243129 - 1 = [2 ^ 3, 19 ^ 1, 23 ^ 1, 91051843 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (318317243129 - 1) / 2 = 159158621564 from by norm_num]
      have h2 : (3 : ZMod 318317243129) ^ 159158621564 = ((318317243128 : ℕ) : ZMod 318317243129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (318317243129 - 1) / 19 = 16753539112 from by norm_num]
      have h2 : (3 : ZMod 318317243129) ^ 16753539112 = ((99791519226 : ℕ) : ZMod 318317243129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (318317243129 - 1) / 23 = 13839880136 from by norm_num]
      have h2 : (3 : ZMod 318317243129) ^ 13839880136 = ((285332582473 : ℕ) : ZMod 318317243129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_91051843).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (318317243129 - 1) / 91051843 = 3496 from by norm_num]
      have h2 : (3 : ZMod 318317243129) ^ 3496 = ((283826483801 : ℕ) : ZMod 318317243129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_477085099566506296749105907250303 : Nat.Prime 477085099566506296749105907250303 := by
  refine lucas_primality 477085099566506296749105907250303 (10 : ZMod 477085099566506296749105907250303) ?_ (fun q hq hd => ?_)
  · rw [show 477085099566506296749105907250303 - 1 = 477085099566506296749105907250302 from by norm_num]
    reduce_mod_char
  · have e : 477085099566506296749105907250303 - 1 = [2 ^ 1, 11 ^ 1, 487 ^ 1, 318317243129 ^ 1, 139889154706049267 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (477085099566506296749105907250303 - 1) / 2 = 238542549783253148374552953625151 from by norm_num]
      have h2 : (10 : ZMod 477085099566506296749105907250303) ^ 238542549783253148374552953625151 = ((477085099566506296749105907250302 : ℕ) : ZMod 477085099566506296749105907250303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (477085099566506296749105907250303 - 1) / 11 = 43371372687864208795373264295482 from by norm_num]
      have h2 : (10 : ZMod 477085099566506296749105907250303) ^ 43371372687864208795373264295482 = ((432669631729632260622368511401150 : ℕ) : ZMod 477085099566506296749105907250303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (477085099566506296749105907250303 - 1) / 487 = 979640861532867139115207201746 from by norm_num]
      have h2 : (10 : ZMod 477085099566506296749105907250303) ^ 979640861532867139115207201746 = ((125471255263925974766975678415306 : ℕ) : ZMod 477085099566506296749105907250303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_318317243129).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (477085099566506296749105907250303 - 1) / 318317243129 = 1498772403520611846638 from by norm_num]
      have h2 : (10 : ZMod 477085099566506296749105907250303) ^ 1498772403520611846638 = ((182976864680900145459141659159744 : ℕ) : ZMod 477085099566506296749105907250303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_139889154706049267).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (477085099566506296749105907250303 - 1) / 139889154706049267 = 3410450942884106 from by norm_num]
      have h2 : (10 : ZMod 477085099566506296749105907250303) ^ 3410450942884106 = ((392615631690175696865598004510275 : ℕ) : ZMod 477085099566506296749105907250303) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3728689909491716802493036489257959126583802658876113672123055708670439187 : Nat.Prime 3728689909491716802493036489257959126583802658876113672123055708670439187 := by
  refine lucas_primality 3728689909491716802493036489257959126583802658876113672123055708670439187 (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ?_ (fun q hq hd => ?_)
  · rw [show 3728689909491716802493036489257959126583802658876113672123055708670439187 - 1 = 3728689909491716802493036489257959126583802658876113672123055708670439186 from by norm_num]
    reduce_mod_char
  · have e : 3728689909491716802493036489257959126583802658876113672123055708670439187 - 1 = [2 ^ 1, 7 ^ 4, 41 ^ 1, 89 ^ 1, 244781 ^ 1, 1822160764176306369698582099 ^ 1, 477085099566506296749105907250303 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3728689909491716802493036489257959126583802658876113672123055708670439187 - 1) / 2 = 1864344954745858401246518244628979563291901329438056836061527854335219593 from by norm_num]
      have h2 : (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ^ 1864344954745858401246518244628979563291901329438056836061527854335219593 = ((3728689909491716802493036489257959126583802658876113672123055708670439186 : ℕ) : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3728689909491716802493036489257959126583802658876113672123055708670439187 - 1) / 7 = 532669987070245257499005212751137018083400379839444810303293672667205598 from by norm_num]
      have h2 : (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ^ 532669987070245257499005212751137018083400379839444810303293672667205598 = ((438717769667343676679543860772431553913522566227212991914403134989635704 : ℕ) : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3728689909491716802493036489257959126583802658876113672123055708670439187 - 1) / 41 = 90943656329066263475439914372145344550824455094539357856659895333425346 from by norm_num]
      have h2 : (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ^ 90943656329066263475439914372145344550824455094539357856659895333425346 = ((3362185110662718367356584554513232402157405225654365707225276317986268618 : ℕ) : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3728689909491716802493036489257959126583802658876113672123055708670439187 - 1) / 89 = 41895392241479964072955466171437742995323625380630490698011861895173474 from by norm_num]
      have h2 : (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ^ 41895392241479964072955466171437742995323625380630490698011861895173474 = ((2081102589619973578243763037898120354122164768288478767479828013691360267 : ℕ) : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3728689909491716802493036489257959126583802658876113672123055708670439187 - 1) / 244781 = 15232758708771174243479013850167942473410120307034098529391806180506 from by norm_num]
      have h2 : (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ^ 15232758708771174243479013850167942473410120307034098529391806180506 = ((3112659740836877719633511509706133812610516541115736902392424704336387862 : ℕ) : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1822160764176306369698582099).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3728689909491716802493036489257959126583802658876113672123055708670439187 - 1) / 1822160764176306369698582099 = 2046301282959103849952597194954710480399130214 from by norm_num]
      have h2 : (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ^ 2046301282959103849952597194954710480399130214 = ((2858659851288790496312169582280641899946426354284453187405835958577280771 : ℕ) : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_477085099566506296749105907250303).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3728689909491716802493036489257959126583802658876113672123055708670439187 - 1) / 477085099566506296749105907250303 = 7815565635731896244353228715248277626862 from by norm_num]
      have h2 : (2 : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) ^ 7815565635731896244353228715248277626862 = ((1090678518629573257013480718551170893443570073389103796787559150230403292 : ℕ) : ZMod 3728689909491716802493036489257959126583802658876113672123055708670439187) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 : Nat.Prime 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 := by
  refine lucas_primality 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 (2 : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) ?_ (fun q hq hd => ?_)
  · rw [show 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1 = 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140506 from by norm_num]
    reduce_mod_char
  · have e : 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 41 ^ 1, 205006741598811803341 ^ 1, 3728689909491716802493036489257959126583802658876113672123055708670439187 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1) / 2 = 3102726262666920083966246010965651945919701633675576132387297583355210480366176633279306386570253 from by norm_num]
      have h2 : (2 : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) ^ 3102726262666920083966246010965651945919701633675576132387297583355210480366176633279306386570253 = ((6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140506 : ℕ) : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1) / 3 = 2068484175111280055977497340643767963946467755783717421591531722236806986910784422186204257713502 from by norm_num]
      have h2 : (2 : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) ^ 2068484175111280055977497340643767963946467755783717421591531722236806986910784422186204257713502 = ((5282595790974593802779152838418187853016342474002531834253972857081968515749697857456541940162462 : ℕ) : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1) / 11 = 564132047757621833448408365630118535621763933395559296797690469700947360066577569687146615740046 from by norm_num]
      have h2 : (2 : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) ^ 564132047757621833448408365630118535621763933395559296797690469700947360066577569687146615740046 = ((2489176526897504144310474761742773855852459944425466942018019251259730684436268615183751354949937 : ℕ) : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1) / 41 = 151352500617898540681280293217836680288765933350028104018892565041717584408106177233136896905866 from by norm_num]
      have h2 : (2 : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) ^ 151352500617898540681280293217836680288765933350028104018892565041717584408106177233136896905866 = ((3464561515525966509758014195733958839206030415765765458719233580694607778372158787624606654823748 : ℕ) : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_205006741598811803341).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1) / 205006741598811803341 = 30269504685253757002638470219796112189607309984756290790294966242986625320066 from by norm_num]
      have h2 : (2 : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) ^ 30269504685253757002638470219796112189607309984756290790294966242986625320066 = ((2895287781005590210206559750952817239364594242095034563224606938710670228336347474287922184996621 : ℕ) : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3728689909491716802493036489257959126583802658876113672123055708670439187).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 - 1) / 3728689909491716802493036489257959126583802658876113672123055708670439187 = 1664244728299154219522238 from by norm_num]
      have h2 : (2 : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) ^ 1664244728299154219522238 = ((3849756133581798402820336089711485417737504128605869833369589743753961489214437937914237808471107 : ℕ) : ZMod 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 : Nat.Prime 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 := by
  refine lucas_primality 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ?_ (fun q hq hd => ?_)
  · rw [show 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1 = 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129400 from by norm_num]
    reduce_mod_char
  · have e : 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 2, 17 ^ 1, 229 ^ 1, 499 ^ 1, 6953201 ^ 1, 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 2 = 25145741428162272202013546686680317560531540790608432327101074043250072097539581862074053137760836930541408564700 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 25145741428162272202013546686680317560531540790608432327101074043250072097539581862074053137760836930541408564700 = ((50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129400 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 3 = 16763827618774848134675697791120211707021027193738954884734049362166714731693054574716035425173891287027605709800 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 16763827618774848134675697791120211707021027193738954884734049362166714731693054574716035425173891287027605709800 = ((15059861774942649651552271111162989482003954626256809446056870639846025765901757327980525686514195730665213241061 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 5 = 10058296571264908880805418674672127024212616316243372930840429617300028839015832744829621255104334772216563425880 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 10058296571264908880805418674672127024212616316243372930840429617300028839015832744829621255104334772216563425880 = ((5458144688664968426182261944511904482745218466149512378320650851782286238909266657434014261759453942912901215418 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 17 = 2958322520960267317883946669021213830650769504777462626717773416852949658534068454361653310324804344769577478200 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 2958322520960267317883946669021213830650769504777462626717773416852949658534068454361653310324804344769577478200 = ((39168642122004699639699657513150686680717930622079104188081837280570994049102814345676890774025434098410850436501 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 229 = 219613462254692333642039709053976572581061491621034343468131651032751721375891544646934961901841370572414048600 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 219613462254692333642039709053976572581061491621034343468131651032751721375891544646934961901841370572414048600 = ((44840886921322146544412158007393869206821749918652047298203196427872238870658742183852110618761464486500834787536 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 499 = 100784534782213515839733654054830932106338840844121973254914124421843976342844015479254721995033414551268170600 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 100784534782213515839733654054830932106338840844121973254914124421843976342844015479254721995033414551268170600 = ((1330279464729113309844748891857449678409 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 6953201 = 7232853308328717148264100717548742675648680597787531908570189195810698438759236749253776250035296529049400 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 7232853308328717148264100717548742675648680597787531908570189195810698438759236749253776250035296529049400 = ((20573111674788543453099960212138305270973767755108366459098622336967687818324036501262898776372759599227092450142 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 - 1) / 6205452525333840167932492021931303891839403267351152264774595166710420960732353266558612773140507 = 8104402161004200 from by norm_num]
      have h2 : (19 : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) ^ 8104402161004200 = ((4763190475843513753245600738459601203230678779011948935281175549337825572606358921917065658977804596756648565579 : ℕ) : ZMod 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_224068983959 : Nat.Prime 224068983959 := by
  refine lucas_primality 224068983959 (7 : ZMod 224068983959) ?_ (fun q hq hd => ?_)
  · rw [show 224068983959 - 1 = 224068983958 from by norm_num]
    reduce_mod_char
  · have e : 224068983959 - 1 = [2 ^ 1, 170707 ^ 1, 656297 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (224068983959 - 1) / 2 = 112034491979 from by norm_num]
      have h2 : (7 : ZMod 224068983959) ^ 112034491979 = ((224068983958 : ℕ) : ZMod 224068983959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (224068983959 - 1) / 170707 = 1312594 from by norm_num]
      have h2 : (7 : ZMod 224068983959) ^ 1312594 = ((25469845307 : ℕ) : ZMod 224068983959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (224068983959 - 1) / 656297 = 341414 from by norm_num]
      have h2 : (7 : ZMod 224068983959) ^ 341414 = ((123316910447 : ℕ) : ZMod 224068983959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_138922770054581 : Nat.Prime 138922770054581 := by
  refine lucas_primality 138922770054581 (2 : ZMod 138922770054581) ?_ (fun q hq hd => ?_)
  · rw [show 138922770054581 - 1 = 138922770054580 from by norm_num]
    reduce_mod_char
  · have e : 138922770054581 - 1 = [2 ^ 2, 5 ^ 1, 31 ^ 1, 224068983959 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138922770054581 - 1) / 2 = 69461385027290 from by norm_num]
      have h2 : (2 : ZMod 138922770054581) ^ 69461385027290 = ((138922770054580 : ℕ) : ZMod 138922770054581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138922770054581 - 1) / 5 = 27784554010916 from by norm_num]
      have h2 : (2 : ZMod 138922770054581) ^ 27784554010916 = ((53379821138465 : ℕ) : ZMod 138922770054581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138922770054581 - 1) / 31 = 4481379679180 from by norm_num]
      have h2 : (2 : ZMod 138922770054581) ^ 4481379679180 = ((41784954999014 : ℕ) : ZMod 138922770054581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_224068983959).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138922770054581 - 1) / 224068983959 = 620 from by norm_num]
      have h2 : (2 : ZMod 138922770054581) ^ 620 = ((49551799611018 : ℕ) : ZMod 138922770054581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5650241619715768498259 : Nat.Prime 5650241619715768498259 := by
  refine lucas_primality 5650241619715768498259 (2 : ZMod 5650241619715768498259) ?_ (fun q hq hd => ?_)
  · rw [show 5650241619715768498259 - 1 = 5650241619715768498258 from by norm_num]
    reduce_mod_char
  · have e : 5650241619715768498259 - 1 = [2 ^ 1, 11 ^ 1, 19 ^ 1, 97301 ^ 1, 138922770054581 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5650241619715768498259 - 1) / 2 = 2825120809857884249129 from by norm_num]
      have h2 : (2 : ZMod 5650241619715768498259) ^ 2825120809857884249129 = ((5650241619715768498258 : ℕ) : ZMod 5650241619715768498259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5650241619715768498259 - 1) / 11 = 513658329065069863478 from by norm_num]
      have h2 : (2 : ZMod 5650241619715768498259) ^ 513658329065069863478 = ((4146676940333032137277 : ℕ) : ZMod 5650241619715768498259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5650241619715768498259 - 1) / 19 = 297381137879777289382 from by norm_num]
      have h2 : (2 : ZMod 5650241619715768498259) ^ 297381137879777289382 = ((1732830686062815944678 : ℕ) : ZMod 5650241619715768498259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5650241619715768498259 - 1) / 97301 = 58069717882814858 from by norm_num]
      have h2 : (2 : ZMod 5650241619715768498259) ^ 58069717882814858 = ((3561816628851814727962 : ℕ) : ZMod 5650241619715768498259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_138922770054581).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5650241619715768498259 - 1) / 138922770054581 = 40671818 from by norm_num]
      have h2 : (2 : ZMod 5650241619715768498259) ^ 40671818 = ((2953401439679291648363 : ℕ) : ZMod 5650241619715768498259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- 3^499 + 1: 7^2 divides 3821 + 1 (chain 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 -> 5650241619715768498259 -> 3821).
theorem kill3_e499 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 499 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 : 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 ∈ P := S7 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 prime_50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 499 = 3 ^ 200 * (3 ^ 200 * 3 ^ 99) by rw [← pow_add, ← pow_add]]; norm_num : 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 ∣ 1 + 3 ^ 499).trans hd)
  have g5650241619715768498259 : 5650241619715768498259 ∈ P := S1 5650241619715768498259 prime_5650241619715768498259 (by norm_num) (hnz (by norm_num)) 50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 g50291482856324544404027093373360635121063081581216864654202148086500144195079163724148106275521673861082817129401 (by norm_num)
  have g3821 : 3821 ∈ P := S1 3821 (by norm_num) (by norm_num) (hnz (by norm_num)) 5650241619715768498259 g5650241619715768498259 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3821 g3821 (by norm_num)

theorem H2_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1.H2 :=
  ⟨0, fun n h hiff he _ =>
    (kill_at h hiff (fun _ _ hP E => kill3_e499 hP E (by rw [he]))).elim⟩

end OMA.Erdos1052E499

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1.H2 := OMA.Erdos1052E499.H2_proof
