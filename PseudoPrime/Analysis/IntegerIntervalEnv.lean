/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalExpressions

/-! # Arithmetic expressions over a finite real input environment -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Checked arithmetic syntax over n real input slots. Atom indices select a
finite input function; constant and nonlinear nodes store proposed output
intervals. Recursive checking and containment of all inputs are the invariants
needed by soundness. The syntax supports continuous scalar cell certificates. -/
inductive IntegerEnvExpr (n : ℕ) where
  | atom (index : Fin n)
  | constant (p d : ℤ) (out : IntegerInterval)
  | add (left right : IntegerEnvExpr n)
  | neg (arg : IntegerEnvExpr n)
  | mul (left right : IntegerEnvExpr n) (out : IntegerInterval)
  | invPos (arg : IntegerEnvExpr n) (out : IntegerInterval)
  | invNeg (arg : IntegerEnvExpr n) (out : IntegerInterval)
  | sqrt (arg : IntegerEnvExpr n) (out : IntegerInterval)

/-- Interpret an expression under a real input assignment rho. Proposed output
intervals do not affect the value. This is the mathematical expression enclosed
by the checked integer computation. -/
noncomputable def IntegerEnvExpr.value {n : ℕ} (e : IntegerEnvExpr n) (ρ : Fin n → ℝ) : ℝ :=
  match e with
  | .atom i => ρ i
  | .constant p d _ => (p : ℝ) / d
  | .add a b => a.value ρ + b.value ρ
  | .neg a => -a.value ρ
  | .mul a b _ => a.value ρ * b.value ρ
  | .invPos a _ => (a.value ρ)⁻¹
  | .invNeg a _ => (a.value ρ)⁻¹
  | .sqrt a _ => Real.sqrt (a.value ρ)

/-- Compute the proposed result under an interval assignment E. Atom intervals
come from E; addition and negation compute endpoints, while other nodes retain
their witnesses. The result is certified only together with a successful check. -/
def IntegerEnvExpr.interval {n : ℕ} (e : IntegerEnvExpr n) (E : Fin n → IntegerInterval) :
    IntegerInterval :=
  match e with
  | .atom i => E i
  | .constant _ _ out => out
  | .add a b => (a.interval E).add (b.interval E)
  | .neg a => (a.interval E).neg
  | .mul _ _ out => out
  | .invPos _ out => out
  | .invNeg _ out => out
  | .sqrt _ out => out

/-- Recursively check all arithmetic witnesses at scale G under input intervals E.
Atom nodes require no computation: their real containment is supplied separately.
Products, reciprocals and square roots use the existing primitive checkers. -/
def IntegerEnvExpr.check {n : ℕ} (e : IntegerEnvExpr n) (G : ℤ) (E : Fin n → IntegerInterval) :
    Bool :=
  match e with
  | .atom _ => true
  | .constant p d out => integerConstantCheck G p d out.lower out.upper
  | .add a b => a.check G E && b.check G E
  | .neg a => a.check G E
  | .mul a b out =>
    a.check G E && b.check G E &&
      integerProductCheck G (a.interval E).lower (a.interval E).upper (b.interval E).lower
        (b.interval E).upper out.lower out.upper
  | .invPos a out =>
    a.check G E &&
      integerReciprocalCheck G (a.interval E).lower (a.interval E).upper out.lower out.upper
  | .invNeg a out =>
    a.check G E &&
      integerNegReciprocalCheck G (a.interval E).lower (a.interval E).upper out.lower out.upper
  | .sqrt a out =>
    a.check G E && integerSqrtCheck G (a.interval E).lower (a.interval E).upper out.lower out.upper

/-- If every real input lies in its assigned interval and the recursive check
succeeds, the computed result interval contains the interpreted real value.
Structural induction composes the primitive soundness theorems, including the
atom case, without assuming any numerical table to be correct. -/
theorem IntegerEnvExpr.check_sound {n : ℕ} (e : IntegerEnvExpr n) (G : ℤ) (ρ : Fin n → ℝ)
    (E : Fin n → IntegerInterval) (hE : ∀ i, (E i).Contains G (ρ i)) (h : e.check G E = true) :
    (e.interval E).Contains G (e.value ρ) := by
  induction e with
  | atom i => exact hE i
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
