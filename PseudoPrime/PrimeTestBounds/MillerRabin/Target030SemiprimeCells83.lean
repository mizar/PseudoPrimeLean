/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030FactorTypes

/-! # Semiprime witnesses on the 83 prescribed closed intervals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The 83 rational closed intervals from the low-scale semiprime plan, in
order from logarithmic scale 8 through 150. -/
def target030Cells83 : List (ℚ × ℚ) :=
  [(8 / 1, 837 / 100), (837 / 100, 8743 / 1000), (8743 / 1000, 9079 / 1000),
    (9079 / 1000, 1883 / 200), (1883 / 200, 9751 / 1000), (9751 / 1000, 10059 / 1000),
    (10059 / 1000, 10499 / 1000), (10499 / 1000, 10909 / 1000), (10909 / 1000, 11293 / 1000),
    (11293 / 1000, 291 / 25), (291 / 25, 5981 / 500), (5981 / 500, 2457 / 200),
    (2457 / 200, 318 / 25), (318 / 25, 13117 / 1000), (13117 / 1000, 13461 / 1000),
    (13461 / 1000, 13871 / 1000), (13871 / 1000, 14241 / 1000), (14241 / 1000, 3661 / 250),
    (3661 / 250, 20219 / 1000), (20219 / 1000, 1291 / 50), (1291 / 50, 32347 / 1000),
    (32347 / 1000, 38999 / 1000), (38999 / 1000, 45353 / 1000), (45353 / 1000, 52303 / 1000),
    (52303 / 1000, 58939 / 1000), (58939 / 1000, 65751 / 1000), (65751 / 1000, 17987 / 250),
    (17987 / 250, 77287 / 1000), (77287 / 1000, 82137 / 1000), (82137 / 1000, 86421 / 1000),
    (86421 / 1000, 9051 / 100), (9051 / 100, 9511 / 100), (9511 / 100, 99373 / 1000),
    (99373 / 1000, 2582 / 25), (2582 / 25, 10659 / 100), (10659 / 100, 54927 / 500),
    (54927 / 500, 56437 / 500), (56437 / 500, 23117 / 200), (23117 / 200, 29519 / 250),
    (29519 / 250, 15121 / 125), (15121 / 125, 123667 / 1000), (123667 / 1000, 126087 / 1000),
    (126087 / 1000, 128357 / 1000), (128357 / 1000, 5213 / 40), (5213 / 40, 132169 / 1000),
    (132169 / 1000, 33461 / 250), (33461 / 250, 135427 / 1000), (135427 / 1000, 6837 / 50),
    (6837 / 50, 137849 / 1000), (137849 / 1000, 27769 / 200), (27769 / 200, 139667 / 1000),
    (139667 / 1000, 140393 / 1000), (140393 / 1000, 140957 / 1000), (140957 / 1000, 70743 / 500),
    (70743 / 500, 70943 / 500), (70943 / 500, 14227 / 100), (14227 / 100, 142591 / 1000),
    (142591 / 1000, 143399 / 1000), (143399 / 1000, 18008 / 125), (18008 / 125, 144651 / 1000),
    (144651 / 1000, 7257 / 50), (7257 / 50, 145519 / 1000), (145519 / 1000, 145893 / 1000),
    (145893 / 1000, 146209 / 1000), (146209 / 1000, 29331 / 200), (29331 / 200, 73533 / 500),
    (73533 / 500, 147403 / 1000), (147403 / 1000, 147699 / 1000), (147699 / 1000, 36993 / 250),
    (36993 / 250, 74141 / 500), (74141 / 500, 148563 / 1000), (148563 / 1000, 148773 / 1000),
    (148773 / 1000, 18618 / 125), (18618 / 125, 149093 / 1000), (149093 / 1000, 149231 / 1000),
    (149231 / 1000, 74681 / 500), (74681 / 500, 149489 / 1000), (149489 / 1000, 149559 / 1000),
    (149559 / 1000, 149653 / 1000), (149653 / 1000, 18713 / 125), (18713 / 125, 37433 / 250),
    (37433 / 250, 74951 / 500), (74951 / 500, 150 / 1)]

/-- Check that adjacent rational intervals have a common endpoint. -/
def target030CellsChain : List (ℚ × ℚ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.2 = b.1) && target030CellsChain (b :: rest)

set_option maxRecDepth 8192 in
/-- The interval list has 83 entries, consecutive endpoints, the specified
endpoints 8 and 150, and nondecreasing endpoints above 8. -/
theorem target030Cells83_checked :
    target030Cells83.length = 83 ∧
      target030CellsChain target030Cells83 = true ∧
      target030Cells83.head? = some (8, 837 / 100) ∧
      target030Cells83.getLast? = some (74951 / 500, 150) ∧
      target030Cells83.all (fun c ↦ decide (8 ≤ c.1 ∧ c.1 ≤ c.2)) = true := by
  decide +kernel

/-- Under GRH, each of the 83 prescribed closed intervals supplies a 0.30
rejecting prime for a distinct odd semiprime. The stronger all-scale
nonuniform theorem provides the witness on each cell. -/
theorem target030_semiprime_cell_witness {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (c : ℚ × ℚ)
    (hc : c ∈ target030Cells83) (hL : (c.1 : ℝ) ≤ Real.log n) (_hU : Real.log n ≤ (c.2 : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcheck := target030Cells83_checked.2.2.2.2
  have hlo : (8 : ℚ) ≤ c.1 := (of_decide_eq_true ((List.all_eq_true.mp hcheck) c hc)).1
  have hloR : (8 : ℝ) ≤ c.1 := by exact_mod_cast hlo
  exact exists_prime_reject_03_semiprime_log8 hn ho hp hq hpq hprod hGRH (hloR.trans hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
