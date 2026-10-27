/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SymmetricPhaseCharacterBounds
public import PseudoPrime.LLS.LogarithmicPhaseJacobiBounds

/-! # Jacobi witness extraction with symmetric quadratic phase cost -/

@[expose] public section

namespace PseudoPrime.LLS

open AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, actual odd-nonsquare Jacobi data and two symmetric logarithmic
anchor bounds, absence of negative witnesses forces the ramp-minus-principal value
below the old local budget with delta=5*d^2/4. Retain the original prime-power
prefix and ambient local costs and use the quadratic character bound. -/
theorem jacobi_no_negative_symmetric_phase_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (d : ℚ)
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u)
    (hminus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x - d) : ℝ) : ℂ))).re ≤
          Analysis.finiteSignedResolvent l t)
    (hplus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x + d) : ℝ) : ℂ))).re ≤
          Analysis.finiteSignedResolvent l t)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      logarithmicPhaseJacobiLocalBudget bridge q x b l ((5 / 4) * d ^ 2) := by
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) (gamma_jacobi_modulus_ge_three bridge)).ne'⟩
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  have hc :=
    PaperStatements.gamma_primitive_sum_re_le_symmetric_anchor_prefix hq
      (gamma_jacobi_modulus_ge_three bridge) hmq hGRH bridge.character_primitive
      bridge.character_ne_one hinv hx l hl d hW (Finset.Ioc 0 ⌊b⌋₊) hminus hplus
  have ha := gamma_jacobi_no_negative_ramp_comparison bridge (by linarith only [hx]) hno
  have he :=
    finiteSigned_character_prefix_add_ambient_ramp_eq_local_cost l bridge.character
      (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge
        (fun p hp ho hpb ↦ hno p hp ho (hpb.trans hbx)))
      x
  dsimp only [logarithmicPhaseJacobiLocalBudget]
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hc ⊢
  linarith only [hc, ha, he]

/-- Under the symmetric-anchor hypotheses, a strict gap above the quadratic
local budget produces an odd-prime negative Jacobi witness through 99*x/40.
Contradict the no-witness comparison. Both endpoint spectral bounds and the scalar
gap remain explicit inputs until a concrete interval is certified. -/
theorem exists_odd_prime_negative_of_symmetric_phase_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (d : ℚ)
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u)
    (hminus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x - d) : ℝ) : ℂ))).re ≤
          Analysis.finiteSignedResolvent l t)
    (hplus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x + d) : ℝ) : ℂ))).re ≤
          Analysis.finiteSignedResolvent l t)
    (hgap :
      logarithmicPhaseJacobiLocalBudget bridge q x b l ((5 / 4) * d ^ 2) <
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
        (jacobi_no_negative_symmetric_phase_comparison bridge hGRH hq hmq hx hb hbx l hl d hW hminus
          hplus hno))
      hgap

end PseudoPrime.LLS
