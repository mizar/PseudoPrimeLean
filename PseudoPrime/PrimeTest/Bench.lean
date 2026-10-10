/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest
public meta import PseudoPrime.PrimeTest

/-!
# Baillie--PSW executable benchmarks

Timing code is isolated from logical regression examples and the public API.
-/

@[expose] public section

-- This benchmark module deliberately exports no declarations.
set_option linter.privateModule false

namespace PseudoPrime.PrimeTest.Bench

/--
Test the Boolean predicate on every list entry, returning true on the empty list.
This recursive conjunction aggregates benchmark expectations without changing individual tests.
-/
private def all (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && all p xs

/--
The seven fixed Miller–Rabin bases used by the benchmark: two and six larger bases.
The timing comparison applies all seven at arbitrary input sizes and claims no size-bound proof.
-/
private def bases7 : List ℕ :=
  [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

/--
The first thirteen prime bases, from two through forty-one, for the benchmark
comparison against the seven-base family.
-/
private def bases13 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

/--
Return true exactly when every supplied base passes the executable strong
Miller–Rabin test for `n`. The empty list accepts; this is a benchmark helper.
-/
private def millerBases (n : ℕ) (bases : List ℕ) : Bool :=
  all (strongMillerRabinWithBase n) bases

/--
Run the executable strong Miller–Rabin test at all seven bases in `bases7`.
This fixed-family Boolean is consumed by the combined benchmark.
-/
private def fixedMr7 (n : ℕ) : Bool :=
  millerBases n bases7

/--
Run the executable strong Miller–Rabin test at the thirteen prime bases in `bases13`.
This fixed-family Boolean is consumed by the combined benchmark.
-/
private def fixedMr13 (n : ℕ) : Bool :=
  millerBases n bases13

/--
Conjoin the seven-base and thirteen-base test results for `n`. Shared bases are
intentionally retested, matching the workload measured by `timeFixedMr`.
-/
private def fixedMr7And13 (n : ℕ) : Bool :=
  fixedMr7 n && fixedMr13 n

/--
Ten large composite strong-pseudoprime inputs used to compare fixed Miller–Rabin
families with strengthened BPSW. The timing helpers aggregate MR acceptance and BPSW rejection
on these supplied inputs; the list itself carries no primality evidence.
-/
private def falseCases : List ℕ :=
  [3361424178291189215886152423998831, 6076980930960900072331484121332682067,
    98005444040796948452951861359577774851, 174069801388781243586842378741078911111,
    211378147002083162804606443786924991431, 1061737499082252754277396944381,
    431431087479804442028846411481781, 20676771234932783685720044499703981,
    1610085313692576297492392438479574101, 11081252958410803876664228314425399061]

/--
Small odd sample inputs `[3,5,7,9,11]`, printed by the benchmark smoke evaluation.
The composite nine is intentionally included; this list is not a list of primes.
-/
private def smokeCases : List ℕ :=
  [3, 5, 7, 9, 11]

/--
Check acceptance of the prechecked base-two test on `[2,3,5,7,11]`.
The sample includes the even prime two to exercise its direct precheck branch.
-/
private def smokeParity : Bool :=
  all (fun n => strongMillerRabinBase2WithPrecheck n = true) [2, 3, 5, 7, 11]

/--
The square `1000000007²`, used as a large square input for the precheck timing.
The benchmark repeats this same value rather than sampling distinct squares.
-/
private def largePrimeSquare : ℕ :=
  1000000014000000049

/--
Measure monotonic elapsed milliseconds for the conjunction of both fixed
Miller–Rabin families on the ten supplied large composites. Print whether all inputs pass
and the elapsed time; this IO action provides a runtime benchmark, not a theorem.
-/
private def timeFixedMr : IO Unit := do
  let start ← IO.monoMsNow
  let results := all (fun n => fixedMr7And13 n = true) falseCases
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"fixed MR bases 7+13: result={results}, elapsed_ms={elapsed}"

/--
Time the scalar fast Lucas-U computation at `n+1` for the selected large input
and parameters `P=Q=1`. Print whether the resulting residue is zero and elapsed milliseconds.
-/
private def timeLucasLargest : IO Unit := do
  let n := 3361424178291189215886152423998831
  let start ← IO.monoMsNow
  let result := decide (lucasUZModFast n 1 1 (n + 1) = 0)
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"Lucas U scalar ZMod: result={result}, elapsed_ms={elapsed}"

/--
Time rejection of every supplied large composite by `strengthenedBPSWWheel30`.
Print the aggregate rejection Boolean and monotonic elapsed milliseconds.
-/
private def timeStrengthenedBPSW : IO Unit := do
  let start ← IO.monoMsNow
  let results := all (fun n => strengthenedBPSWWheel30 n = false) falseCases
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"strengthened BPSW: result={results}, elapsed_ms={elapsed}"

/--
Time 1000 repetitions of the large-square precheck and print whether every
result is `some false`, together with elapsed milliseconds. The timer starts after list creation.
-/
private def timeSquarePrecheck : IO Unit := do
  let inputs := List.replicate 1000 largePrimeSquare
  let start ← IO.monoMsNow
  let results := all (fun n => decide (primalityPrecheck n = some false)) inputs
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"large prime square precheck x1000: result={results}, elapsed_ms={elapsed}"

#eval smokeCases

#eval smokeParity

#eval timeFixedMr

#eval timeLucasLargest

#eval timeStrengthenedBPSW

#eval timeSquarePrecheck

end PseudoPrime.PrimeTest.Bench
