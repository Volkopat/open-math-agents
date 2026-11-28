import OMAStatements.S_oeis_a034699

-- Credit: @tjgksruf9801 (shorter proof). Between the consecutive primes 4177 and 4201,
-- a 4180 = a 4199 = 19.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a034699.main) := fun h =>
  absurd (h 4177 4201 (by norm_num) (by norm_num) (by decide)
    (fun r h1 h2 => by interval_cases r <;> norm_num) 4180 4199 (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel)) (by decide)
