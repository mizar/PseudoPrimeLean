/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervals
public import PseudoPrime.Analysis.IntegerIntervalSqrt

/-! # Checked arithmetic expressions over integer intervals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Arithmetic expression with proposed interval witnesses at constants and products.
Addition and negation compute endpoints exactly; all witnesses are checked recursively.
This is the finite arithmetic core for endpoint and scalar certificates. -/
inductive IntegerIntervalExpr where
  | constant (p d : ℤ) (out : IntegerInterval)
  | add (left right : IntegerIntervalExpr)
  | neg (arg : IntegerIntervalExpr)
  | mul (left right : IntegerIntervalExpr) (out : IntegerInterval)
  | invPos (arg : IntegerIntervalExpr) (out : IntegerInterval)
  | invNeg (arg : IntegerIntervalExpr) (out : IntegerInterval)
  | sqrt (arg : IntegerIntervalExpr) (out : IntegerInterval)

/-- The real arithmetic value represented by an expression, independently of its
proposed interval witnesses. Denominator validity is enforced by the checker. -/
noncomputable def IntegerIntervalExpr.value : IntegerIntervalExpr → ℝ
  | .constant p d _ => (p : ℝ) / d
  | .add a b => a.value + b.value
  | .neg a => -a.value
  | .mul a b _ => a.value * b.value
  | .invPos a _ => a.value⁻¹
  | .invNeg a _ => a.value⁻¹
  | .sqrt a _ => Real.sqrt a.value

/-- Compute the output interval from witnesses and exact endpoint operations.
The result is meaningful only together with successful recursive checking. -/
def IntegerIntervalExpr.interval : IntegerIntervalExpr → IntegerInterval
  | .constant _ _ out => out
  | .add a b => a.interval.add b.interval
  | .neg a => a.interval.neg
  | .mul _ _ out => out
  | .invPos _ out => out
  | .invNeg _ out => out
  | .sqrt _ out => out

/-- Check every witness in the expression at common scale `G`. Each child must
succeed; product nodes also validate all four corner comparisons. -/
def IntegerIntervalExpr.check (G : ℤ) : IntegerIntervalExpr → Bool
  | .constant p d out => integerConstantCheck G p d out.lower out.upper
  | .add a b => a.check G && b.check G
  | .neg a => a.check G
  | .mul a b out =>
    a.check G && b.check G &&
      integerProductCheck G a.interval.lower a.interval.upper b.interval.lower b.interval.upper
        out.lower out.upper
  | .invPos a out =>
    a.check G && integerReciprocalCheck G a.interval.lower a.interval.upper out.lower out.upper
  | .invNeg a out =>
    a.check G && integerNegReciprocalCheck G a.interval.lower a.interval.upper out.lower out.upper
  | .sqrt a out =>
    a.check G && integerSqrtCheck G a.interval.lower a.interval.upper out.lower out.upper

/-- Successful recursive checking encloses the expression's real value.
Induct on the expression and compose the primitive interval soundness theorems. -/
theorem IntegerIntervalExpr.check_sound (e : IntegerIntervalExpr) (G : ℤ) (h : e.check G = true) :
    e.interval.Contains G e.value := by
  induction e with
  | constant p d out => exact integerConstantCheck_sound h
  | add a b ha hb =>
    have hc := Bool.and_eq_true_iff.mp h
    exact IntegerInterval.add_contains (ha hc.1) (hb hc.2)
  | neg a ha => exact IntegerInterval.neg_contains (ha h)
  | mul a b out ha hb =>
    have hc := Bool.and_eq_true_iff.mp h
    have hab := Bool.and_eq_true_iff.mp hc.1
    exact IntegerInterval.product_contains hc.2 (ha hab.1) (hb hab.2)
  | invPos a out ha =>
    have hc := Bool.and_eq_true_iff.mp h
    exact integerReciprocalCheck_sound hc.2 (ha hc.1)
  | invNeg a out ha =>
    have hc := Bool.and_eq_true_iff.mp h
    exact integerNegReciprocalCheck_sound hc.2 (ha hc.1)
  | sqrt a out ha =>
    have hc := Bool.and_eq_true_iff.mp h
    exact integerSqrtCheck_sound hc.2 (ha hc.1)

end PseudoPrime.Analysis
