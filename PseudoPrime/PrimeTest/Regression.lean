/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest
public meta import PseudoPrime.PrimeTest

/-!
# Baillie--PSW regression tests

Compiled examples and executable classifications are kept in a dedicated
module so failures are visible without making them part of the public API.
-/

@[expose] public section

-- This regression module deliberately exports no declarations.
set_option linter.privateModule false

namespace PseudoPrime.PrimeTest.Regression

/--
Conjoin a Boolean predicate over the supplied list, accepting the empty list.
Regression evaluations use this helper to aggregate their stated expectations.
-/
private def all (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && all p xs

/--
Ten supplied ordinary Lucas-pseudoprime regression inputs. The evaluations below
check that the wheel-based BPSW variants reject every input; the list stores test data only.
-/
private def lucasCases : List ℕ :=
  [323, 377, 1159, 1829, 3827, 5459, 5777, 9071, 9179, 10877]

/--
Ten supplied strong Lucas-pseudoprime regression inputs used to check rejection
by both wheel-based BPSW variants.
-/
private def strongLucasCases : List ℕ :=
  [5459, 5777, 10877, 16109, 18971, 22499, 24569, 25199, 40309, 58519]

/--
Five supplied Lucas-V pseudoprime inputs used to exercise rejection by the
combined wheel-based tests.
-/
private def lucasVCases : List ℕ :=
  [913, 150267335403, 430558874533, 14760229232131, 936916995253453]

/--
Ten supplied odd composite strong pseudoprimes to base two. Regression checks
contrast acceptance by the prechecked base-two test with rejection by larger base families
and the combined Lucas tests.
-/
private def base2StrongPseudoprimes : List ℕ :=
  [2047, 3277, 4033, 4681, 8321, 15841, 29341, 42799, 49141, 52633]

/--
Seven fixed strong Miller–Rabin bases used by executable regression comparisons.
These checks include inputs far beyond machine-sized deterministic-test ranges.
-/
private def mrBases7 : List ℕ :=
  [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

/--
Thirteen prime strong Miller–Rabin bases from two through forty-one, used for
regression comparisons against the seven-base family.
-/
private def mrBases13 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

/--
The prime `2147483647` as a large input expected to pass both fixed
Miller–Rabin base families.
-/
private def mrPrimeCases : List ℕ :=
  [2147483647]

/--
Ten small odd primes from three through thirty-one, used to check acceptance
by the wheel-based BPSW variants.
-/
private def smallPrimeCases : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/--
Inputs `[7,13,2047]` for comparing Method A and Method A* at discriminant five.
The first two are prime examples and 2047 is composite; the executable assertions check
equality of the two strong-Lucas implementations on each supplied input.
-/
private def methodAStarFiveCases : List ℕ :=
  [7, 13, 2047]

/--
Ten composite constructions supplied as strong pseudoprimes to both fixed
Miller–Rabin base families. Each entry comment records its factorization and construction
parameter; the following evaluations check MR acceptance and BPSW rejection.
-/
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

/--
Check that every supplied base passes the executable strong Miller–Rabin test
for `n`. This Boolean helper preserves the list order and aggregates regression expectations.
-/
private def passesMrBases (n : ℕ) (bases : List ℕ) : Bool :=
  all (fun base => strongMillerRabinWithBase n base = true) bases

/--
The square `1000000007²`, used to exercise square rejection by the primality
precheck and both combined wheel-based tests.
-/
private def largePrimeSquare : ℕ :=
  1000000014000000049

#eval ("lpsp-baillie-psw-false", all (fun n => bailliePSWWheel30 n = false) lucasCases)

#eval ("slpsp-baillie-psw-false", all (fun n => bailliePSWWheel30 n = false) strongLucasCases)

#eval ("vpsp-baillie-psw-false", all (fun n => bailliePSWWheel30 n = false) lucasVCases)

#eval ("lpsp-strengthened-bpsw-false", all (fun n => strengthenedBPSWWheel30 n = false) lucasCases)

#eval
  ("slpsp-strengthened-bpsw-false",
    all (fun n => strengthenedBPSWWheel30 n = false) strongLucasCases)

#eval ("vpsp-strengthened-bpsw-false", all (fun n => strengthenedBPSWWheel30 n = false) lucasVCases)

#eval ("small-primes-baillie-psw-true", all (fun n => bailliePSWWheel30 n = true) smallPrimeCases)

#eval
  ("small-primes-strengthened-bpsw-true",
    all (fun n => strengthenedBPSWWheel30 n = true) smallPrimeCases)

#eval
  ("base2-strong-pseudoprimes-pass-mr",
    all (fun n => strongMillerRabinBase2WithPrecheck n = true) base2StrongPseudoprimes)

#eval
  ("base2-strong-pseudoprimes-fail-baillie-psw",
    all (fun n => bailliePSWWheel30 n = false) base2StrongPseudoprimes)

#eval
  ("base2-strong-pseudoprimes-fail-strengthened-bpsw",
    all (fun n => strengthenedBPSWWheel30 n = false) base2StrongPseudoprimes)

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
    all (fun n => bailliePSWWheel30 n = false) multiBaseStrongPseudoprimes)

#eval
  ("multi-base-pseudoprimes-fail-strengthened-bpsw",
    all (fun n => strengthenedBPSWWheel30 n = false) multiBaseStrongPseudoprimes)

#eval
  ("large-prime-square-precheck-false", decide (primalityPrecheck largePrimeSquare = some false))

#eval ("large-prime-square-baillie-psw-false", decide (bailliePSWWheel30 largePrimeSquare = false))

#eval
  ("large-prime-square-strengthened-bpsw-false",
    decide (strengthenedBPSWWheel30 largePrimeSquare = false))

#eval
  ("method-a-a-star-d5-agree",
    all
      (fun n =>
        strongLucasMethodAStar n 5 (by norm_num only) = strongLucasMethodA n 5 (by norm_num only))
      methodAStarFiveCases)

/- These executable assertions make a false regression result fail elaboration. -/
#eval
  show IO Bool from do
    unless
      (all
        (fun n =>
          strongLucasMethodAStar n 5 (by norm_num only) = strongLucasMethodA n 5 (by norm_num only))
        methodAStarFiveCases) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (all (fun n => strongMillerRabinBase2WithPrecheck n = true) base2StrongPseudoprimes) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (all (fun n => passesMrBases n mrBases7 = false) base2StrongPseudoprimes) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (all (fun n => passesMrBases n mrBases13 = false) base2StrongPseudoprimes) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (all (fun n => passesMrBases n mrBases7 = true) mrPrimeCases) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (all (fun n => passesMrBases n mrBases13 = true) mrPrimeCases) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless
      (all (fun n => strongMillerRabinBase2WithPrecheck n = true) multiBaseStrongPseudoprimes) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (all (fun n => passesMrBases n mrBases7 = true) multiBaseStrongPseudoprimes) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (all (fun n => passesMrBases n mrBases13 = true) multiBaseStrongPseudoprimes) do
      throw (IO.userError "primality regression failed")
    return true

#eval
  show IO Bool from do
    unless (primalityPrecheck largePrimeSquare = some false) do
      throw (IO.userError "primality regression failed")
    return true

#eval bailliePSWWheel30 0

#eval bailliePSWWheel30 1

#eval bailliePSWWheel30 2

#eval strengthenedBPSWWheel30 0

#eval strengthenedBPSWWheel30 1

#eval strengthenedBPSWWheel30 2

end PseudoPrime.PrimeTest.Regression
