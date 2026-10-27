/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.LogIntervalPhaseCharacterBounds
public import PseudoPrime.LLS.LogarithmicPhaseJacobiBounds

/-! # Jacobi comparisons throughout a certified logarithmic scale interval -/

@[expose] public section

namespace PseudoPrime.LLS

open AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, odd-nonsquare Jacobi data, admissible nonnegative Euler
weights and two endpoint spectral bounds, absence of witnesses forces the actual
ramp-minus-principal value below the original local budget with
 delta=5*(r1-r0)^2/16. Apply the interval character bound and the exact ambient
prime-prefix identity. This controls every interior scale under the same endpoints. -/
theorem jacobi_no_negative_log_interval_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (r0 r1 : ℚ) (hlo : (r0 : ℝ) ≤ Real.log x)
    (hhi : Real.log x ≤ (r1 : ℝ)) (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u)
    (ha :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * r0 : ℝ) : ℂ) * Complex.I)).re ≤
          Analysis.finiteSignedResolvent l t)
    (hbphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * r1 : ℝ) : ℂ) * Complex.I)).re ≤
          Analysis.finiteSignedResolvent l t)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      logarithmicPhaseJacobiLocalBudget bridge q x b l ((5 / 16) * (r1 - r0) ^ 2) := by
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) (gamma_jacobi_modulus_ge_three bridge)).ne'⟩
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  have hc :=
    PaperStatements.gamma_primitive_sum_re_le_log_interval_prefix hq
      (gamma_jacobi_modulus_ge_three bridge) hmq hGRH bridge.character_primitive
      bridge.character_ne_one hinv hx l hl r0 r1 hlo hhi hW (Finset.Ioc 0 ⌊b⌋₊) ha hbphase
  have ha := gamma_jacobi_no_negative_ramp_comparison bridge (by linarith only [hx]) hno
  have he :=
    finiteSigned_character_prefix_add_ambient_ramp_eq_local_cost l bridge.character
      (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge
        (fun p hp ho hpb ↦ hno p hp ho (hpb.trans hbx)))
      x
  dsimp only [logarithmicPhaseJacobiLocalBudget]
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_ofNat] at hc ⊢
  linarith only [hc, ha, he]

/-- Under the log-interval endpoint hypotheses, a strict gap above the
local budget yields an odd-prime negative Jacobi witness through 99*x/40.
Contradict the no-witness comparison. Endpoint spectral bounds and the scalar gap
are explicit remaining inputs; no separate interior spectral premise is needed. -/
theorem exists_odd_prime_negative_of_log_interval_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (r0 r1 : ℚ) (hlo : (r0 : ℝ) ≤ Real.log x)
    (hhi : Real.log x ≤ (r1 : ℝ)) (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u)
    (ha :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * r0 : ℝ) : ℂ) * Complex.I)).re ≤
          Analysis.finiteSignedResolvent l t)
    (hbphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * r1 : ℝ) : ℂ) * Complex.I)).re ≤
          Analysis.finiteSignedResolvent l t)
    (hgap :
      logarithmicPhaseJacobiLocalBudget bridge q x b l ((5 / 16) * (r1 - r0) ^ 2) <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  apply Classical.byContradiction
  intro h
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1 :=
    fun p hp ho hpb hj ↦ h ⟨p, hp, ho, hpb, hj⟩
  exact
    (not_lt_of_ge
        (jacobi_no_negative_log_interval_comparison bridge hGRH hq hmq hx hb hbx l hl r0 r1 hlo hhi
          hW ha hbphase hno))
      hgap

end PseudoPrime.LLS
