/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularCore

/-! # Rational triangular profile certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational certificate for a triangular cutoff C L² from the entrance T.
The root floors a and m, fourth-root denominator v, and secondary budget b
satisfy the exact polynomial inequalities consumed by the generic estimates. -/
structure TriangularProfile where
  C : ℝ
  T : ℝ
  a : ℝ
  m : ℝ
  v : ℝ
  b : ℝ
  entry : 30000000000 ≤ T
  root : 1 / 2 < a
  localBudget : 14 < (a - 1 / 2) * T
  square : a ^ 2 ≤ C
  upper : C ≤ 1
  root16 : 0 < m ∧ m ^ 16 ≤ C * T ^ 2
  fourth : 0 < v ∧ v ^ 2 ≤ T
  cost : 165000 + 4000000000000 * (1001 / 1000) / (a * m) ≤ b * T
  triple : 28237 / 100000 ≤ C ∨ (1411811 / 5000000 ≤ C ∧ 1820000000000 ≤ T)
  margin : (36 + b + (1456 + 13 / 10000000) / v) * T + 101 < (68 - 3 / 10000) * a * T

/-- The analytic fields of a triangular profile, excluding its triple certificate.
The core is used by the local and large-index estimates and retains all budgets. -/
def triangularProfileCore (f : TriangularProfile) : TriangularCore where
  C := f.C
  T := f.T
  a := f.a
  m := f.m
  v := f.v
  b := f.b
  entry := f.entry
  root := f.root
  localBudget := f.localBudget
  square := f.square
  upper := f.upper
  root16 := f.root16
  fourth := f.fourth
  cost := f.cost
  margin := f.margin

/-- The first profile has coefficient 7/15 and starts at thirty billion. -/
noncomputable def triangularP0466 : TriangularProfile where
  C := 7 / 15
  T := 30000000000
  a := 6831 / 10000
  m := 19
  v := 170000
  b := 1028337 / 100000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- A certified profile controls the radius, the fourth root, and the scale
uniformly above its entrance. The proof uses monotonicity of nonnegative squares. -/
theorem triangularProfile_roots (f : TriangularProfile) {L : ℝ} (hL : f.T ≤ L) :
    let x := f.C * L ^ 2;
    1 < x ∧ f.a * L ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / f.v := by
  exact triangularCore_roots (triangularProfileCore f) hL

/-- Rational certificate for the coefficient-042 triangular profile. -/
noncomputable def triangularP042 : TriangularProfile where
  C := 21 / 50
  T := 40000000000
  a := 648 / 1000
  m := 20
  v := 200000
  b := 772377 / 100000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- Rational certificate for the coefficient-0333 triangular profile. -/
noncomputable def triangularP0333 : TriangularProfile where
  C := 1 / 3
  T := 100000000000
  a := 5773 / 10000
  m := 22
  v := 300000
  b := 315261 / 100000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- Rational certificate for the coefficient-030 triangular profile. -/
noncomputable def triangularP030 : TriangularProfile where
  C := 3 / 10
  T := 250000000000
  a := 5477 / 10000
  m := 24
  v := 500000
  b := 121843 / 100000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- Rational certificate for the coefficient-029 triangular profile. -/
noncomputable def triangularP029 : TriangularProfile where
  C := 29 / 100
  T := 500000000000
  a := 5385 / 10000
  m := 26
  v := 700000
  b := 57196 / 100000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- Rational certificate for the coefficient-0284 triangular profile. -/
noncomputable def triangularP0284 : TriangularProfile where
  C := 71 / 250
  T := 1080000000000
  a := 532916 / 1000000
  m := 59 / 2
  v := 1000000
  b := 23583 / 100000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- Rational certificate for the coefficient-02829 triangular profile. -/
noncomputable def triangularP02829 : TriangularProfile where
  C := 2829 / 10000
  T := 1480000000000
  a := 531883 / 1000000
  m := 153 / 5
  v := 1000000
  b := 16623 / 100000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- Rational certificate for the coefficient-02823622 triangular profile. -/
noncomputable def triangularP02823622 : TriangularProfile where
  C := 1411811 / 5000000
  T := 1820000000000
  a := 531377 / 1000000
  m := 157 / 5
  v := 1000000
  b := 6593 / 50000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inr ⟨le_rfl, le_rfl⟩
  margin := by norm_num only

/-- The eight certified profiles, in increasing order of their entrances.
Each index selects the corresponding rational cutoff and numerical budget. -/
noncomputable def triangularProfile (i : Fin 8) : TriangularProfile :=
  match i.val with
  | 0 => triangularP0466
  | 1 => triangularP042
  | 2 => triangularP0333
  | 3 => triangularP030
  | 4 => triangularP029
  | 5 => triangularP0284
  | 6 => triangularP02829
  | _ => triangularP02823622

/-- The negative power splits into reciprocal root factors. Its certified
sixteenth-root floor and radius slope give the generic decaying-cost estimate. -/
theorem triangularProfile_power (f : TriangularProfile) {L : ℝ} (hL : f.T ≤ L) :
    (f.C * L ^ 2) ^ (-9 / 16 : ℝ) ≤ (1 / f.a / L) * (1 / f.m) := by
  exact triangularCore_power (triangularProfileCore f) hL

/-- Above its entrance, each profile bounds the signed secondary cost by b L
and the pole correction by 100. The ratio (L+284)/L is at most 1001/1000. -/
theorem triangularProfile_costs (f : TriangularProfile) {L : ℝ} (hL : f.T ≤ L) :
    let x := f.C * L ^ 2;
    165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ f.b * L ∧
      36 * L / (Real.sqrt x - 1) ≤ 100 := by
  exact triangularCore_costs (triangularProfileCore f) hL

/-- The certified positive rational margin gives the actual alpha-18 signed
gap for every subgroup index at least 10^12. The independent cost is divided
by that index; all scale-dependent errors retain the profile's own v. -/
theorem triangularProfile_gap (f : TriangularProfile) {L h : ℝ} (hL : f.T ≤ L)
    (hh : 1000000000000 ≤ h) :
    let x := f.C * L ^ 2;
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
        (h - 1) * (36 * L + 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  exact triangularCore_gap (triangularProfileCore f) hL hh

end PseudoPrime.PrimeTestBounds.MillerRabin
