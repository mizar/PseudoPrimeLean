/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.WeightedEndpointReduction
public import PseudoPrime.NumberTheory.QuadraticSignPatterns

/-! # Actual biquadratic trace penalties and endpoint comparison

Independent nonprincipal quadratic characters realize all three nonidentity unit-sign
patterns. Consequently the canonical penalty is the true worst trace value for arbitrary
normalized nonnegative weights. Actual conductor costs, principal prefixes and full tails
then connect this finite classification to the endpoint reduction and least-prime criterion.
The strict analytic gap remains explicit; closed conductor envelopes are provided separately.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A real sum over three distinct selected characters expands into its three terms.
Input: distinctness of the two characters and their product, plus any real summand.
Expand the finite insertions. This supports arbitrary actual family weights. -/
private theorem sum_biquadratic_family {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (f : DirichletCharacter ℂ q → ℝ) :
    (∑ ψ ∈ NumberTheory.quadraticTriple a b, f ψ) = f a + f b + f (a * b) := by
  classical
  have hA : a ∉ ({b, a * b} : Finset (DirichletCharacter ℂ q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hab, ha, or_self, not_false_eq_true]
  have hB : b ∉ ({a * b} : Finset (DirichletCharacter ℂ q)) := fun h ↦
    hb (Finset.mem_singleton.mp h)
  rw [NumberTheory.quadraticTriple, Finset.sum_insert hA, Finset.sum_insert hB,
    Finset.sum_singleton, add_assoc]

/-- The actual three-character weighted trace equals its three individual contributions.
Input: distinct nonprincipal labels, arbitrary weights and a residue. Expand the finite
family sum. This does not impose a chosen weight profile or equal weights. -/
theorem biquadratic_trace_eq {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ) (z : ZMod q) :
    NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z =
      w a * (a z).re + w b * (b z).re + w (a * b) * ((a * b) z).re :=
  sum_biquadratic_family a b hab (left_ne_mul.mpr hb1) (right_ne_mul.mpr ha1) _

/-- The actual selected family total equals its three individual weights.
Input: distinct nonprincipal character labels and arbitrary weights. Expand the finite sum.
This transfers actual normalization to the simplex coordinates. -/
theorem biquadratic_weight_total {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ) :
    NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w =
      w a + w b + w (a * b) :=
  sum_biquadratic_family a b hab (left_ne_mul.mpr hb1) (right_ne_mul.mpr ha1) _

/-- The actual selected conductor cost is the weighted sum of its three conductor logs.
Input: distinct nonprincipal labels and arbitrary weights. Expand the finite sum.
This connects an arbitrary original weight function to the exact endpoint costs. -/
theorem biquadratic_weight_cost {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ) :
    NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b) w =
      w a * Real.log a.conductor + w b * Real.log b.conductor +
        w (a * b) * Real.log (a * b).conductor :=
  sum_biquadratic_family a b hab (left_ne_mul.mpr hb1) (right_ne_mul.mpr ha1) _

/-- The minus/plus sign pattern realizes the penalty determined by the second weight.
Input: a normalized actual family and the two character values at a residue. Their product
has negative sign. Expand the trace and use normalization to evaluate its exact value. -/
private theorem biquadratic_trace_first {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w = 1) (z : ZMod q)
    (ha : a z = -1) (hb : b z = 1) :
    NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z =
      -(1 - 2 * w b) := by
  have hn := (biquadratic_weight_total a b hab ha1 hb1 w).symm.trans hW
  rw [biquadratic_trace_eq a b hab ha1 hb1 w, MulChar.mul_apply, ha, hb, mul_one, Complex.neg_re,
    Complex.one_re]
  nlinarith only [hn]

/-- The plus/minus sign pattern realizes the penalty determined by the first weight.
Input: a normalized actual family and the two character values at a residue. Expand the
trace including the negative product value and use the exact weight sum. -/
private theorem biquadratic_trace_second {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w = 1) (z : ZMod q)
    (ha : a z = 1) (hb : b z = -1) :
    NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z =
      -(1 - 2 * w a) := by
  have hn := (biquadratic_weight_total a b hab ha1 hb1 w).symm.trans hW
  rw [biquadratic_trace_eq a b hab ha1 hb1 w, MulChar.mul_apply, ha, hb, one_mul, Complex.neg_re,
    Complex.one_re]
  nlinarith only [hn]

/-- The two-negative sign pattern realizes the product-weight penalty.
Input: a normalized actual family and two negative character values. Their product value
is positive. Expand the trace and use normalization to evaluate this third endpoint. -/
private theorem biquadratic_trace_third {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w = 1) (z : ZMod q)
    (ha : a z = -1) (hb : b z = -1) :
    NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z =
      -(1 - 2 * w (a * b)) := by
  have hn := (biquadratic_weight_total a b hab ha1 hb1 w).symm.trans hW
  rw [biquadratic_trace_eq a b hab ha1 hb1 w, MulChar.mul_apply, ha, hb, neg_mul_neg, one_mul,
    Complex.neg_re, Complex.one_re]
  nlinarith only [hn]

/-- Three individual weight penalties bound the penalty at their minimum weight.
Input: all three affine bounds. The nested minimum equals one of its three arguments.
Use that exact choice. This converts realized trace patterns to the canonical penalty. -/
private theorem penalty_min_bound {wa wb wc m : ℝ} (ha : 1 - 2 * wa ≤ m) (hb : 1 - 2 * wb ≤ m)
    (hc : 1 - 2 * wc ≤ m) : 1 - 2 * min wa (min wb wc) ≤ m :=
  Or.elim (min_choice wa (min wb wc)) (fun h ↦ h.symm ▸ ha)
    (fun h ↦ h.symm ▸ Or.elim (min_choice wb wc) (fun h' ↦ h'.symm ▸ hb) (fun h' ↦ h'.symm ▸ hc))

/-- The product of the two mixed-sign units has two negative character signs.
Input: actual minus/plus and plus/minus units. Evaluate each character multiplicatively.
This supplies the third realized nonidentity biquadratic pattern. -/
private theorem negative_product_signs {q : ℕ} (a b : DirichletCharacter ℂ q) (u v : (ZMod q)ˣ)
    (hau : a (u : ZMod q) = -1) (hbu : b (u : ZMod q) = 1) (hav : a (v : ZMod q) = 1)
    (hbv : b (v : ZMod q) = -1) :
    a ((u * v : (ZMod q)ˣ) : ZMod q) = -1 ∧ b ((u * v : (ZMod q)ˣ) : ZMod q) = -1 :=
  ⟨(map_mul a (u : ZMod q) (v : ZMod q)).trans
      ((congrArg₂ (fun x y : ℂ ↦ x * y) hau hav).trans (mul_one (-1))),
    (map_mul b (u : ZMod q) (v : ZMod q)).trans
      ((congrArg₂ (fun x y : ℂ ↦ x * y) hbu hbv).trans (one_mul (-1)))⟩

/-- An actual independent-quadratic trace certificate bounds the canonical minimum penalty.
Input: distinct nonprincipal quadratic characters, actual total one and a global trace
certificate. Choose the two mixed-sign units and their product; they realize all three
affine penalties. Select the minimum weight to obtain the exact necessary bound. -/
theorem biquadratic_penalty_necessary {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hqa : a.IsQuadratic) (hqb : b.IsQuadratic)
    (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w = 1) {m : ℝ}
    (htrace :
      ∀ z : ZMod q,
        -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z) :
    1 - 2 * min (w a) (min (w b) (w (a * b))) ≤ m :=
  Exists.elim (NumberTheory.quadratic_unit_sign_patterns a b hqa hqb ha1 hb1 hab) fun u hu ↦
    Exists.elim hu fun v hv ↦
      let hp := negative_product_signs a b u v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
      penalty_min_bound
        (neg_le_neg_iff.mp
          ((htrace v).trans_eq (biquadratic_trace_second a b hab ha1 hb1 w hW v hv.2.2.1 hv.2.2.2)))
        (neg_le_neg_iff.mp
          ((htrace u).trans_eq (biquadratic_trace_first a b hab ha1 hb1 w hW u hv.1 hv.2.1)))
        (neg_le_neg_iff.mp
          ((htrace (u * v : (ZMod q)ˣ)).trans_eq
            (biquadratic_trace_third a b hab ha1 hb1 w hW (u * v) hp.1 hp.2)))

/-- Nonnegative actual family weights give three nonnegative simplex coordinates.
Input: family-wise nonnegativity. Apply it to the two selected characters and their product.
This supplies the coordinates used by the existing endpoint reduction. -/
private theorem biquadratic_weight_nonneg {q : ℕ} (a b : DirichletCharacter ℂ q)
    (w : DirichletCharacter ℂ q → ℝ) (hw : ∀ ψ ∈ NumberTheory.quadraticTriple a b, 0 ≤ w ψ) :
    0 ≤ w a ∧ 0 ≤ w b ∧ 0 ≤ w (a * b) :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  ⟨hw a (Finset.mem_insert_self _ _), hw b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
    hw (a * b) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩

/-- Projecting an actual weight function to its three selected values preserves the trace.
Input: distinct nonprincipal labels, weights and a residue. Both finite sums expand into
the same three terms. This reuses the proved general quadratic-profile trace bound. -/
private theorem biquadratic_profile_trace {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ) (z : ZMod q) :
    NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b)
        (NumberTheory.quadraticTripleWeight a b (w a) (w b) (w (a * b))) z =
      NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z :=
  (NumberTheory.quadraticTripleTrace_eq a b hab (left_ne_mul.mpr hb1) (right_ne_mul.mpr ha1) (w a)
        (w b) (w (a * b)) z).trans
    (biquadratic_trace_eq a b hab ha1 hb1 w z).symm

/-- Projecting actual weights to the three selected values preserves conductor cost.
Input: distinct nonprincipal labels and arbitrary weights. Compare the exact three-term
cost expansions. This connects actual profiles to the established scalar endpoint theorem. -/
private theorem biquadratic_profile_cost {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (w : DirichletCharacter ℂ q → ℝ) :
    NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
        (NumberTheory.quadraticTripleWeight a b (w a) (w b) (w (a * b))) =
      NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b) w :=
  (NumberTheory.quadraticTripleWeight_cost a b hab (left_ne_mul.mpr hb1) (right_ne_mul.mpr ha1)
        (w a) (w b) (w (a * b))).trans
    (biquadratic_weight_cost a b hab ha1 hb1 w).symm

/-- The actual normalized biquadratic trace has its canonical minimum-weight lower bound.
Input: independent nonprincipal quadratic labels, nonnegative actual weights and total one.
Project to the three selected values and use the proved finite quadratic trace bound.
This is the sufficiency direction of the exact penalty characterization. -/
theorem biquadratic_trace_lower {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hqa : a.IsQuadratic) (hqb : b.IsQuadratic) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ NumberTheory.quadraticTriple a b, 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w = 1) (z : ZMod q) :
    -(1 - 2 * min (w a) (min (w b) (w (a * b)))) ≤
      NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z := by
  have hg := biquadratic_weight_nonneg a b w hw
  have hn := (biquadratic_weight_total a b hab ha1 hb1 w).symm.trans hW
  have hl :=
    NumberTheory.quadraticTripleTrace_lower a b hab (left_ne_mul.mpr hb1) (right_ne_mul.mpr ha1) hqa
      hqb hg.1 hg.2.1 hg.2.2 z
  rw [hn, biquadratic_profile_trace a b hab ha1 hb1 w z] at hl
  nlinarith only [hl]

/-- The four biquadratic endpoints dominate every admissible actual weighted deficit.
Input: arbitrary nonnegative normalized family weights and an actual trace certificate.
Realized sign patterns force its penalty above the canonical value. Apply the existing
exact conductor/prefix reduction and the actual nonnegative principal tail. No separate
scalar penalty assumption is retained. -/
theorem biquadratic_actual_endpoint (K : MellinKernel) {q : ℕ} [NeZero q]
    (a b : DirichletCharacter ℂ q) (hab : a ≠ b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hqa : a.IsQuadratic)
    (hqb : b.IsQuadratic) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ NumberTheory.quadraticTriple a b, 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w = 1) {m x : ℝ}
    (htrace :
      ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z)
    (hx : 0 < x) (E : ℝ) (T : Finset ℕ) :
    let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let F := (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let ca := K.mass * Real.log a.conductor + E
    let cb := K.mass * Real.log b.conductor + E
    let cc := K.mass * Real.log (a * b).conductor + E
    min (min (ca - P + (F - P)) (cb - P + (F - P)))
        (min (cc - P + (F - P)) ((ca + cb + cc) / 3 - P + (F - P) / 3)) ≤
      K.mass * NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b) w + E - P +
        m * (F - P) := by
  dsimp only
  have hg := biquadratic_weight_nonneg a b w hw
  have hn := (biquadratic_weight_total a b hab ha1 hb1 w).symm.trans hW
  have hb :=
    quadratic_prefix_endpoint K a b hab (left_ne_mul.mpr hb1) (right_ne_mul.mpr ha1) hg.1 hg.2.1
      hg.2.2 hn x E T
  rw [biquadratic_profile_cost a b hab ha1 hb1 w] at hb
  have hm := biquadratic_penalty_necessary a b hab ha1 hb1 hqa hqb w hW htrace
  exact
    hb.trans
      (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right hm (principal_tail_nonneg K (q := q) hx T)))

/-- The canonical minimum-weight penalty exactly characterizes the actual trace bound.
Input: independent nonprincipal quadratic labels and arbitrary normalized nonnegative
weights. The three realized unit-sign patterns prove necessity; the finite trace theorem
proves sufficiency. This completes the arbitrary-profile penalty optimization. -/
theorem biquadratic_trace_iff {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hqa : a.IsQuadratic) (hqb : b.IsQuadratic) (w : DirichletCharacter ℂ q → ℝ)
    (hw : ∀ ψ ∈ NumberTheory.quadraticTriple a b, 0 ≤ w ψ)
    (hW : NumberTheory.characterWeightTotal (NumberTheory.quadraticTriple a b) w = 1) {m : ℝ} :
    (∀ z : ZMod q,
        -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z) ↔
      1 - 2 * min (w a) (min (w b) (w (a * b))) ≤ m :=
  ⟨biquadratic_penalty_necessary a b hab ha1 hb1 hqa hqb w hW, fun hm z ↦
    (neg_le_neg hm).trans (biquadratic_trace_lower a b hab ha1 hb1 hqa hqb w hw hW z)⟩

/-- The three selected independent quadratic characters are all nonprincipal.
Input: nonprincipal distinct labels and quadraticity of the second. A trivial product
would identify the first with the second's inverse, which equals the second itself.
This supplies actual family admissibility for the prime criterion. -/
private theorem biquadratic_nonprincipal {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hqb : b.IsQuadratic) :
    ∀ ψ ∈ NumberTheory.quadraticTriple a b, ψ ≠ 1 :=
  let hi : b = b⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr (pow_two b ▸ (MulChar.isQuadratic_iff_sq_eq_one.mp hqb))
  let hp : a * b ≠ 1 := fun h ↦ hab ((eq_inv_iff_mul_eq_one.mpr h).trans hi.symm)
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  fun _ hψ ↦
  Or.elim (Finset.mem_insert.mp hψ) (fun h ↦ h.symm ▸ ha1)
    (fun h ↦
      Or.elim (Finset.mem_insert.mp h) (fun h ↦ h.symm ▸ hb1)
        (fun h ↦ (Finset.mem_singleton.mp h).symm ▸ hp))

/-- The three selected characters annihilate the common unit kernel.
Input: the two labels. Kernel membership makes each label one on the intersection, and
annihilator closure handles their product. This supplies the exact target subgroup. -/
private theorem biquadratic_annihilates {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q) :
    ∀ ψ ∈ NumberTheory.quadraticTriple a b,
      ψ ∈ NumberTheory.subgroupAnnihilator (a.toUnitHom.ker ⊓ b.toUnitHom.ker) :=
  let H := a.toUnitHom.ker ⊓ b.toUnitHom.ker
  let ha : a ∈ NumberTheory.subgroupAnnihilator H :=
    (NumberTheory.mem_subgroupAnnihilator_iff H a).mpr fun u hu ↦
      (MulChar.coe_toUnitHom a u).symm.trans (congrArg Units.val (MonoidHom.mem_ker.mp hu.1))
  let hb : b ∈ NumberTheory.subgroupAnnihilator H :=
    (NumberTheory.mem_subgroupAnnihilator_iff H b).mpr fun u hu ↦
      (MulChar.coe_toUnitHom b u).symm.trans (congrArg Units.val (MonoidHom.mem_ker.mp hu.2))
  NumberTheory.quadraticTriple_annihilates H a b ha hb

/-- A negative canonical biquadratic deficit gives an actual least outside prime under GRH.
Input: independent nonprincipal quadratic labels and arbitrary nonnegative normalized
weights with a supported principal prefix. Supply the proved canonical trace certificate
and actual family admissibility to the common weighted criterion. Uniform constants and
thresholds are retained; the analytic strict gap remains explicit. -/
theorem biquadratic_least_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ a b : DirichletCharacter ℂ q,
                      a ≠ b →
                        a ≠ 1 →
                          b ≠ 1 →
                            a.IsQuadratic →
                              b.IsQuadratic →
                                ∀ w : DirichletCharacter ℂ q → ℝ,
                                  (∀ ψ ∈ NumberTheory.quadraticTriple a b, 0 ≤ w ψ) →
                                    NumberTheory.characterWeightTotal
                                          (NumberTheory.quadraticTriple a b) w =
                                        1 →
                                      ∀ X x : ℝ,
                                        2 ≤ x →
                                          ∀ T : Finset ℕ,
                                            (∀ n ∈ T, (n : ℝ) ≤ X) →
                                              let P :=
                                                ∑ n ∈ T,
                                                  (MellinKernel.summand K
                                                      (1 : DirichletCharacter ℂ q) x n).re
                                              let F :=
                                                (∑' n : ℕ,
                                                    MellinKernel.summand K
                                                      (1 : DirichletCharacter ℂ q) x n).re
                                              let E :=
                                                η * Real.log q +
                                                  C * (1 + Real.log q * Real.log x / Real.sqrt x)
                                              let m := 1 - 2 * min (w a) (min (w b) (w (a * b)))
                                              K.mass *
                                                          NumberTheory.weightedConductorLogSum
                                                            (NumberTheory.quadraticTriple a b) w +
                                                        E -
                                                      P +
                                                    m * (F - P) <
                                                  0 →
                                                ∃ p : ℕ,
                                                  IsLeast
                                                      (NumberTheory.primesOutside q
                                                        (a.toUnitHom.ker ⊓ b.toUnitHom.ker))
                                                      p ∧
                                                    (p : ℝ) ≤ X := by
  obtain ⟨C, hC, hb⟩ := weighted_least_prime_criterion K hg
  refine ⟨C, hC, fun η hη ↦ ?_⟩
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq a b hab ha1 hb1 hqa hqb w hw hW X x hx T hT P F E m hgap
  have htrace :
    ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b) w z :=
    biquadratic_trace_lower a b hab ha1 hb1 hqa hqb w hw hW
  apply
    hb q hq (a.toUnitHom.ker ⊓ b.toUnitHom.ker) (NumberTheory.quadraticTriple a b) w hw
      (biquadratic_nonprincipal a b hab ha1 hb1 hqb) (biquadratic_annihilates a b) m X x hx htrace T
      hT
  rw [hW, mul_one]
  change
    K.mass * NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b) w + E <
      (1 + m) * P - m * F
  nlinarith only [hgap]

/-- Any admissible actual biquadratic strict gap yields a least outside prime under GRH.
Input: arbitrary normalized nonnegative weights, an actual trace certificate and supported
prefix. The realized unit patterns make the canonical deficit no larger, using principal
tail nonnegativity. Apply the canonical least-prime criterion without an extra penalty premise. -/
theorem biquadratic_optimal_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ a b : DirichletCharacter ℂ q,
                      a ≠ b →
                        a ≠ 1 →
                          b ≠ 1 →
                            a.IsQuadratic →
                              b.IsQuadratic →
                                ∀ w : DirichletCharacter ℂ q → ℝ,
                                  (∀ ψ ∈ NumberTheory.quadraticTriple a b, 0 ≤ w ψ) →
                                    NumberTheory.characterWeightTotal
                                          (NumberTheory.quadraticTriple a b) w =
                                        1 →
                                      ∀ m : ℝ,
                                        (∀ z : ZMod q,
                                            -m ≤
                                              NumberTheory.weightedCharacterTrace
                                                (NumberTheory.quadraticTriple a b) w z) →
                                          ∀ X x : ℝ,
                                            2 ≤ x →
                                              ∀ T : Finset ℕ,
                                                (∀ n ∈ T, (n : ℝ) ≤ X) →
                                                  let P :=
                                                    ∑ n ∈ T,
                                                      (MellinKernel.summand K
                                                          (1 : DirichletCharacter ℂ q) x n).re
                                                  let F :=
                                                    (∑' n : ℕ,
                                                        MellinKernel.summand K
                                                          (1 : DirichletCharacter ℂ q) x n).re
                                                  let E :=
                                                    η * Real.log q +
                                                      C *
                                                        (1 + Real.log q * Real.log x / Real.sqrt x)
                                                  K.mass *
                                                              NumberTheory.weightedConductorLogSum
                                                                (NumberTheory.quadraticTriple a b)
                                                                w +
                                                            E -
                                                          P +
                                                        m * (F - P) <
                                                      0 →
                                                    ∃ p : ℕ,
                                                      IsLeast
                                                          (NumberTheory.primesOutside q
                                                            (a.toUnitHom.ker ⊓ b.toUnitHom.ker))
                                                          p ∧
                                                        (p : ℝ) ≤ X :=
  Exists.elim (biquadratic_least_criterion K hg) fun C hC ↦
    ⟨C, hC.1, fun η hη ↦
      Exists.elim (hC.2 η hη) fun Q hQ ↦
        ⟨Q, hQ.1, fun q _ hq a b hab ha1 hb1 hqa hqb w hw hW _m htrace X x hx T hT hgap ↦
          let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
          let E := η * Real.log q + C * (1 + Real.log q * Real.log x / Real.sqrt x)
          let hm := biquadratic_penalty_necessary a b hab ha1 hb1 hqa hqb w hW htrace
          let ht :=
            principal_tail_nonneg K (q := q) ((show (0 : ℝ) < 2 from zero_lt_two).trans_le hx) T
          hQ.2 q hq a b hab ha1 hb1 hqa hqb w hw hW X x hx T hT
            ((add_le_add
                  (le_refl
                    (K.mass *
                          NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
                            w +
                        E -
                      P))
                  (mul_le_mul_of_nonneg_right hm ht)).trans_lt
              hgap)⟩⟩

end PseudoPrime.LLS.PaperStatements
