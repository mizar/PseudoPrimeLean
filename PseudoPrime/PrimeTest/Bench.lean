import PseudoPrime.PrimeTest

/-!
# Baillie--PSW executable benchmarks

Timing code is isolated from logical regression examples and the public API.
-/

namespace PseudoPrime.PrimeTest.Bench

private def all (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && all p xs

private def bases7 : List ℕ :=
  [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

private def bases13 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

private def millerBases (n : ℕ) (bases : List ℕ) : Bool :=
  all (strongMillerRabinWithBase n) bases

private def fixedMr7 (n : ℕ) : Bool :=
  millerBases n bases7

private def fixedMr13 (n : ℕ) : Bool :=
  millerBases n bases13

private def fixedMr7And13 (n : ℕ) : Bool :=
  fixedMr7 n && fixedMr13 n

private def falseCases : List ℕ :=
  [3361424178291189215886152423998831, 6076980930960900072331484121332682067,
    98005444040796948452951861359577774851, 174069801388781243586842378741078911111,
    211378147002083162804606443786924991431, 1061737499082252754277396944381,
    431431087479804442028846411481781, 20676771234932783685720044499703981,
    1610085313692576297492392438479574101, 11081252958410803876664228314425399061]

private def smokeCases : List ℕ :=
  [3, 5, 7, 9, 11]

private def smokeParity : Bool :=
  all (fun n => strongMillerRabinBase2WithPrecheck n = true) [2, 3, 5, 7, 11]

private def largePrimeSquare : ℕ :=
  1000000014000000049

private def timeFixedMr : IO Unit := do
  let start ← IO.monoMsNow
  let results := all (fun n => fixedMr7And13 n = true) falseCases
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"fixed MR bases 7+13: result={results}, elapsed_ms={elapsed}"

private def timeLucasLargest : IO Unit := do
  let n := 3361424178291189215886152423998831
  let start ← IO.monoMsNow
  let result := decide (lucasUZModFast n 1 1 (n + 1) = 0)
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"Lucas U scalar ZMod: result={result}, elapsed_ms={elapsed}"

private def timeStrengthenedBPSW : IO Unit := do
  let start ← IO.monoMsNow
  let results := all (fun n => strengthenedBPSW n = false) falseCases
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"strengthened BPSW: result={results}, elapsed_ms={elapsed}"

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
