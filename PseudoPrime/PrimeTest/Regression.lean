import PseudoPrime.PrimeTest

/-!
# Baillie--PSW regression tests

Compiled examples and executable classifications are kept in a dedicated
module so failures are visible without making them part of the public API.
-/

namespace PseudoPrime.PrimeTest.Regression

private def all (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && all p xs

private def lucasCases : List ℕ :=
  [323, 377, 1159, 1829, 3827, 5459, 5777, 9071, 9179, 10877]

private def strongLucasCases : List ℕ :=
  [5459, 5777, 10877, 16109, 18971, 22499, 24569, 25199, 40309, 58519]

private def lucasVCases : List ℕ :=
  [913, 150267335403, 430558874533, 14760229232131, 936916995253453]

/- Known odd composite strong pseudoprimes to the single base `2`. -/
private def base2StrongPseudoprimes : List ℕ :=
  [2047, 3277, 4033, 4681, 8321, 15841, 29341, 42799, 49141, 52633]

private def mrBases7 : List ℕ :=
  [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

private def mrBases13 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

private def mrPrimeCases : List ℕ :=
  [2147483647]

private def smallPrimeCases : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/- D = 5 Method A/A* equivalence examples: primes 7 and 13, composite 2047. -/
private def methodAStarFiveCases : List ℕ :=
  [7, 13, 2047]

/- Composite numbers constructed as strong pseudoprimes for the fixed MR bases.
   Each comment records the factorization and the parameter `m`. -/
private def multiBaseStrongPseudoprimes : List ℕ :=
  [ /- n = 3361424178291189215886152423998831
      = 21116326471 * 358977549991 * 443442855871
      = (m + 1)(17m + 1)(21m + 1), m = 21116326470. -/
      3361424178291189215886152423998831,
    /- n = 6076980930960900072331484121332682067
      = 257240820307 * 4373093945203 * 5402057226427
      = (m + 1)(17m + 1)(21m + 1), m = 257240820306. -/
    6076980930960900072331484121332682067,
    /- n = 98005444040796948452951861359577774851
      = 977282901739 * 4886414508691 * 20522940936499
      = (m + 1)(5m + 1)(21m + 1), m = 977282901738. -/
    98005444040796948452951861359577774851,
    /- n = 174069801388781243586842378741078911111
      = 163403390791 * 19118196722431 * 55720556259391
      = (m + 1)(117m + 1)(341m + 1), m = 163403390790. -/
    174069801388781243586842378741078911111,
    /- n = 211378147002083162804606443786924991431
      = 53321508631 * 37378377549631 * 106056480665071
      = (m + 1)(701m + 1)(1989m + 1), m = 53321508630. -/
    211378147002083162804606443786924991431,
    /- n = 1061737499082252754277396944381
      = 728607404259061 * 1457214808518121
      = m(2m - 1), m = 728607404259061. -/
    1061737499082252754277396944381,
    /- n = 431431087479804442028846411481781
      = 14687257870000861 * 29374515740001721
      = m(2m - 1), m = 14687257870000861. -/
    431431087479804442028846411481781,
    /- n = 20676771234932783685720044499703981
      = 101677852148176261 * 203355704296352521
      = m(2m - 1), m = 101677852148176261. -/
    20676771234932783685720044499703981,
    /- n = 1610085313692576297492392438479574101
      = 897241693662464701 * 1794483387324929401
      = m(2m - 1), m = 897241693662464701. -/
    1610085313692576297492392438479574101,
    /- n = 11081252958410803876664228314425399061
      = 2353853538180615421 * 4707707076361230841
      = m(2m - 1), m = 2353853538180615421. -/
    11081252958410803876664228314425399061]

private def passesMrBases (n : ℕ) (bases : List ℕ) : Bool :=
  all (fun base => strongMillerRabinWithBase n base = true) bases

private def largePrimeSquare : ℕ :=
  1000000014000000049

#eval ("lpsp-baillie-psw-false", all (fun n => bailliePSW n = false) lucasCases)

#eval ("slpsp-baillie-psw-false", all (fun n => bailliePSW n = false) strongLucasCases)

#eval ("vpsp-baillie-psw-false", all (fun n => bailliePSW n = false) lucasVCases)

#eval ("lpsp-strengthened-bpsw-false", all (fun n => strengthenedBPSW n = false) lucasCases)

#eval ("slpsp-strengthened-bpsw-false", all (fun n => strengthenedBPSW n = false) strongLucasCases)

#eval ("vpsp-strengthened-bpsw-false", all (fun n => strengthenedBPSW n = false) lucasVCases)

#eval ("small-primes-baillie-psw-true", all (fun n => bailliePSW n = true) smallPrimeCases)

#eval
  ("small-primes-strengthened-bpsw-true", all (fun n => strengthenedBPSW n = true) smallPrimeCases)

#eval
  ("base2-strong-pseudoprimes-pass-mr",
    all (fun n => strongMillerRabinBase2WithPrecheck n = true) base2StrongPseudoprimes)

#eval
  ("base2-strong-pseudoprimes-fail-baillie-psw",
    all (fun n => bailliePSW n = false) base2StrongPseudoprimes)

#eval
  ("base2-strong-pseudoprimes-fail-strengthened-bpsw",
    all (fun n => strengthenedBPSW n = false) base2StrongPseudoprimes)

#eval
  ("base2-strong-pseudoprimes-fail-mr-bases7",
    all (fun n => passesMrBases n mrBases7 = false) base2StrongPseudoprimes)

#eval
  ("base2-strong-pseudoprimes-fail-mr-bases13",
    all (fun n => passesMrBases n mrBases13 = false) base2StrongPseudoprimes)

#eval ("large-prime-pass-mr-bases7", all (fun n => passesMrBases n mrBases7 = true) mrPrimeCases)

#eval ("large-prime-pass-mr-bases13", all (fun n => passesMrBases n mrBases13 = true) mrPrimeCases)

#eval
  ("multi-base-pseudoprimes-pass-base2-mr",
    all (fun n => strongMillerRabinBase2WithPrecheck n = true) multiBaseStrongPseudoprimes)

#eval
  ("multi-base-pseudoprimes-pass-mr-bases7",
    all (fun n => passesMrBases n mrBases7 = true) multiBaseStrongPseudoprimes)

#eval
  ("multi-base-pseudoprimes-pass-mr-bases13",
    all (fun n => passesMrBases n mrBases13 = true) multiBaseStrongPseudoprimes)

#eval
  ("multi-base-pseudoprimes-fail-strong-lucas-via-bpsw",
    all (fun n => bailliePSW n = false) multiBaseStrongPseudoprimes)

#eval
  ("multi-base-pseudoprimes-fail-strengthened-bpsw",
    all (fun n => strengthenedBPSW n = false) multiBaseStrongPseudoprimes)

#eval
  ("large-prime-square-precheck-false", decide (primalityPrecheck largePrimeSquare = some false))

#eval ("large-prime-square-baillie-psw-false", decide (bailliePSW largePrimeSquare = false))

#eval
  ("large-prime-square-strengthened-bpsw-false", decide (strengthenedBPSW largePrimeSquare = false))

#eval
  ("method-a-a-star-d5-agree",
    all (fun n => strongLucasMethodAStar n 5 (by norm_num) = strongLucasMethodA n 5 (by norm_num))
      methodAStarFiveCases)

/- These assertions make a false regression result fail compilation. -/
example : all (fun n => bailliePSW n = false) lucasCases := by native_decide

example : all (fun n => bailliePSW n = false) strongLucasCases := by native_decide

example : all (fun n => bailliePSW n = false) lucasVCases := by native_decide

example : all (fun n => strengthenedBPSW n = false) lucasCases := by native_decide

example : all (fun n => strengthenedBPSW n = false) strongLucasCases := by native_decide

example : all (fun n => strengthenedBPSW n = false) lucasVCases := by native_decide

example :
    all (fun n => strongLucasMethodAStar n 5 (by norm_num) = strongLucasMethodA n 5 (by norm_num))
      methodAStarFiveCases := by
  native_decide

example : all (fun n => bailliePSW n = true) smallPrimeCases := by native_decide

example : all (fun n => strengthenedBPSW n = true) smallPrimeCases := by native_decide

example : all (fun n => strongMillerRabinBase2WithPrecheck n = true) base2StrongPseudoprimes := by
  native_decide

example : all (fun n => bailliePSW n = false) base2StrongPseudoprimes := by native_decide

example : all (fun n => strengthenedBPSW n = false) base2StrongPseudoprimes := by native_decide

example : all (fun n => passesMrBases n mrBases7 = false) base2StrongPseudoprimes := by
  native_decide

example : all (fun n => passesMrBases n mrBases13 = false) base2StrongPseudoprimes := by
  native_decide

example : all (fun n => passesMrBases n mrBases7 = true) mrPrimeCases := by native_decide

example : all (fun n => passesMrBases n mrBases13 = true) mrPrimeCases := by native_decide

example :
    all (fun n => strongMillerRabinBase2WithPrecheck n = true) multiBaseStrongPseudoprimes := by
  native_decide

example : all (fun n => passesMrBases n mrBases7 = true) multiBaseStrongPseudoprimes := by
  native_decide

example : all (fun n => passesMrBases n mrBases13 = true) multiBaseStrongPseudoprimes := by
  native_decide

example : all (fun n => bailliePSW n = false) multiBaseStrongPseudoprimes := by native_decide

example : all (fun n => strengthenedBPSW n = false) multiBaseStrongPseudoprimes := by native_decide

example : primalityPrecheck largePrimeSquare = some false := by native_decide

example : bailliePSW largePrimeSquare = false := by native_decide

example : strengthenedBPSW largePrimeSquare = false := by native_decide

#eval bailliePSW 0

#eval bailliePSW 1

#eval bailliePSW 2

#eval strengthenedBPSW 0

#eval strengthenedBPSW 1

#eval strengthenedBPSW 2

example : ∀ n : ℕ, n ≠ 2 → Even n → bailliePSW n = false := by
  intro n hn2 heven
  exact bailliePSW_even_false hn2 heven

example : strengthenedBPSW 0 = false ∧ strengthenedBPSW 1 = false ∧ strengthenedBPSW 2 = true := by
  exact ⟨strengthenedBPSW_zero, strengthenedBPSW_one, strengthenedBPSW_two⟩

example : ∀ n : ℕ, n ≠ 2 → Even n → strengthenedBPSW n = false := by
  intro n hn2 heven
  exact strengthenedBPSW_even_false hn2 heven

example : PrimalityTestSpec bailliePSW :=
  bailliePSW_spec_unconditional

example : PrimalityTestSpec strengthenedBPSW :=
  strengthenedBPSW_spec_unconditional

end PseudoPrime.PrimeTest.Regression
