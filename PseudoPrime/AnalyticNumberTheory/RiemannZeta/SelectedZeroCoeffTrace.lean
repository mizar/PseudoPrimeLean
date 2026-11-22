/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroCoeffStep

/-! # All checked coefficient steps for a selected zero -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Record the degree and both output intervals at every step of a coefficient
chain, including the initial coefficient. The recursive traversal preserves
the witness order and does not retrieve elements by index. -/
@[expose]
def phaseCoeffTrace (k : ℕ) (R I : Analysis.IntegerInterval) :
    List PhaseCoeffWitness → List (ℕ × Analysis.IntegerInterval × Analysis.IntegerInterval)
  | [] => [(k, R, I)]
  | w :: rest => (k, R, I) :: phaseCoeffTrace (k + 1) w.imagProd.neg w.realProd rest

/-- Each degree through the length of a witness chain occurs in its trace.
The proof traverses the chain without indexing it; it supplies the matching
intervals when a checked trace is connected to a finite coefficient sum. -/
theorem phaseCoeffTrace_degree (chain : List PhaseCoeffWitness) (k d : ℕ)
    (R I : Analysis.IntegerInterval) (hd : d ≤ chain.length) :
    ∃ R' I', (k + d, R', I') ∈ phaseCoeffTrace k R I chain := by
  induction chain generalizing k d R I with
  | nil =>
    have h : d = 0 := Nat.eq_zero_of_le_zero hd
    subst d
    exact ⟨R, I, by simp only [phaseCoeffTrace, Nat.add_zero, List.mem_singleton]⟩
  | cons w rest ih =>
    cases d with
    | zero => exact ⟨R, I, by simp only [phaseCoeffTrace, Nat.add_zero, List.mem_cons, true_or]⟩
    | succ
      d =>
      have hd' : d ≤ rest.length :=
        Nat.le_of_succ_le_succ (by simpa only [List.length_cons] using hd)
      obtain ⟨R', I', he⟩ := ih (k + 1) d w.imagProd.neg w.realProd hd'
      refine ⟨R', I', ?_⟩
      simp only [phaseCoeffTrace, List.mem_cons]
      right
      simpa only [Nat.add_succ, Nat.succ_add] using he

/-- Every row of a successfully checked coefficient trace encloses the
coefficient at its recorded degree. The proof traverses the witness chain once
and propagates the shared initial amplitude through the checked products. -/
theorem phaseCoeffTrace_sound (chain : List PhaseCoeffWitness) (G p d : ℤ) (k : ℕ)
    (R I : Analysis.IntegerInterval) (A : ℂ) (h : phaseCoeffCheck G p d k R I chain = true)
    (hz :
      Analysis.complexIntervalContains R I G
        (A * (((((p : ℝ) / d : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)))) :
    ∀ e ∈ phaseCoeffTrace k R I chain,
      Analysis.complexIntervalContains e.2.1 e.2.2 G
        (A * (((((p : ℝ) / d : ℝ) : ℂ) * Complex.I) ^ e.1 / (e.1.factorial : ℂ))) := by
  induction chain generalizing k R I with
  | nil =>
    intro e he
    have he' := List.mem_singleton.mp he
    subst e
    exact hz
  | cons w rest ih =>
    intro e he
    have hm := List.mem_cons.mp he
    rcases hm with heq | he'
    · subst e
      exact hz
    · have h1 := Bool.and_eq_true_iff.mp h
      have h2 := Bool.and_eq_true_iff.mp h1.1
      have h3 := Bool.and_eq_true_iff.mp h2.1
      have hd := Analysis.integerConstantCheck_sound h3.1
      have hd' : w.step.Contains G ((p : ℝ) / d / (k + 1)) := by
        simpa only [Analysis.IntegerInterval.Contains, Int.cast_mul, Int.cast_add, Int.cast_natCast,
          Int.cast_one, div_mul_eq_div_div] using hd
      have hn := phase_coeff_step_contains A ((p : ℝ) / d) k hz hd' h3.2 h2.2
      exact ih (k + 1) w.imagProd.neg w.realProd h1.2 hn e he'

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
