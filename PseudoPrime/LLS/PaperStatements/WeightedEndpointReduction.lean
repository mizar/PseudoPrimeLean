/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.WeightedCharacterPrimeBounds
public import PseudoPrime.NumberTheory.QuadraticTraceWeights

/-! # Endpoint reduction of finite weighted LLS deficits

The scalar deficits in this module compare selected character families against a common
principal prefix and tail. Their role is specific to the LLS weighted prime criterion.
The finite character identities remain in the independent NumberTheory trace module.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The minimum of four costs is below every nonnegative normalized weighted average.
Input: four real costs and four nonnegative weights summing to one.
Proof: multiply the four minimum inequalities and add.
Role: reduce the finite LLS comparison deficit to certified endpoint candidates. -/
private theorem min_four_weighted {a b c d r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hu : 0 ≤ u) (h : r + s + t + u = 1) :
    min (min a b) (min c d) ≤ r * a + s * b + t * c + u * d := by
  have ha :=
    mul_le_mul_of_nonneg_left ((min_le_left (min a b) (min c d)).trans (min_le_left a b)) hr
  have hb :=
    mul_le_mul_of_nonneg_left ((min_le_left (min a b) (min c d)).trans (min_le_right a b)) hs
  have hc :=
    mul_le_mul_of_nonneg_left ((min_le_right (min a b) (min c d)).trans (min_le_left c d)) ht
  have hd :=
    mul_le_mul_of_nonneg_left ((min_le_right (min a b) (min c d)).trans (min_le_right c d)) hu
  nlinarith only [ha, hb, hc, hd, congrArg (fun v : ℝ ↦ v * min (min a b) (min c d)) h]

/-- Subtracting the minimum weight leaves a nonnegative normalized four-endpoint mixture.
Input: three nonnegative weights summing to one. Claim: the residual weights and three times
that minimum form a simplex point. Proof: the minimum inequalities and one affine identity.
Role: expose the single-character and equal-weight endpoints of a quadratic deficit. -/
private theorem quadratic_weight_simplex {wa wb wc : ℝ} (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc)
    (hw : wa + wb + wc = 1) :
    let t := min wa (min wb wc)
    0 ≤ wa - t ∧ 0 ≤ wb - t ∧ 0 ≤ wc - t ∧ 0 ≤ 3 * t ∧ (wa - t) + (wb - t) + (wc - t) + 3 * t = 1 :=
  ⟨sub_nonneg.mpr (min_le_left _ _), sub_nonneg.mpr ((min_le_right _ _).trans (min_le_left _ _)),
    sub_nonneg.mpr ((min_le_right _ _).trans (min_le_right _ _)),
    mul_nonneg (by norm_num only) (le_min hwa (le_min hwb hwc)), by linarith only [hw]⟩

/-- Every normalized quadratic weighted deficit is at least one endpoint deficit.
Input: nonnegative weights summing to one, three character costs and principal prefix/tail.
Claim: a single-character or uniform three-character endpoint is no worse.
Proof: express the deficit as the normalized mixture induced by the minimum weight.
Role: rule out an improvement from continuous nonnegative weight search at fixed kernel/scale. -/
theorem quadratic_endpoint_deficit {wa wb wc : ℝ} (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc)
    (hw : wa + wb + wc = 1) (ca cb cc P T : ℝ) :
    min (min (ca - P + T) (cb - P + T)) (min (cc - P + T) ((ca + cb + cc) / 3 - P + T / 3)) ≤
      wa * ca + wb * cb + wc * cc - P + (1 - 2 * min wa (min wb wc)) * T := by
  have hc := quadratic_weight_simplex hwa hwb hwc hw
  have hb :=
    min_four_weighted hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 (a := ca - P + T) (b := cb - P + T)
      (c := cc - P + T) (d := (ca + cb + cc) / 3 - P + T / 3)
  nlinarith only [hb, congrArg (fun v : ℝ ↦ v * P) hw, congrArg (fun v : ℝ ↦ v * T) hw]

/-- Compare actual weighted conductor costs with the single and uniform endpoint deficits.
Input: distinct quadratic-family labels, normalized nonnegative weights and common principal
prefix/full-sum data. Claim: one endpoint deficit is no larger than the weighted deficit.
Proof: expand exact conductor costs and apply the normalized scalar reduction.
Role: connect finite character weights to the principal comparison budget. -/
theorem quadratic_character_deficit {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) {wa wb wc : ℝ} (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc)
    (hw : wa + wb + wc = 1) (M P F E : ℝ) :
    let ca := M * Real.log a.conductor + E
    let cb := M * Real.log b.conductor + E
    let cc := M * Real.log (a * b).conductor + E
    min (min (ca - P + (F - P)) (cb - P + (F - P)))
        (min (cc - P + (F - P)) ((ca + cb + cc) / 3 - P + (F - P) / 3)) ≤
      M *
              NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
                (NumberTheory.quadraticTripleWeight a b wa wb wc) +
            E -
          P +
        (1 - 2 * min wa (min wb wc)) * (F - P) := by
  dsimp only
  rw [NumberTheory.quadraticTripleWeight_cost a b hab ha hb]
  have h :=
    quadratic_endpoint_deficit hwa hwb hwc hw (M * Real.log a.conductor + E)
      (M * Real.log b.conductor + E) (M * Real.log (a * b).conductor + E) P (F - P)
  nlinarith only [h, congrArg (fun v : ℝ ↦ v * E) hw]

/-- Normalize the exact quadratic trace penalty by a unit total weight.
Input: quadratic characters and nonnegative weights summing to one.
Proof: substitute the total in the general finite trace bound.
Role: supply the trace certificate inside the actual least-prime criterion. -/
private theorem quadratic_normalized_trace {q : ℕ} (a b : DirichletCharacter ℂ q) (hab : a ≠ b)
    (ha : a ≠ a * b) (hb : b ≠ a * b) (hqa : a.IsQuadratic) (hqb : b.IsQuadratic) {wa wb wc : ℝ}
    (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc) (hw : wa + wb + wc = 1) (z : ZMod q) :
    -(1 - 2 * min wa (min wb wc)) ≤
      NumberTheory.weightedCharacterTrace (NumberTheory.quadraticTriple a b)
        (NumberTheory.quadraticTripleWeight a b wa wb wc) z := by
  have h := NumberTheory.quadraticTripleTrace_lower a b hab ha hb hqa hqb hwa hwb hwc z
  rw [hw] at h
  linarith only [h]

/-- A negative normalized quadratic deficit gives an actual least outside prime under GRH.
Input: quadratic annihilating characters, normalized nonnegative weights and a supported
principal prefix. Claim: a negative actual conductor/prefix deficit gives a least eligible
outside prime below the cutoff, with uniform error constants and modulus threshold.
Proof: supply the proved trace and exact weight total to the general weighted criterion.
Role: distinguish the gap-based criterion from the closed radius bounds in the family envelope. -/
theorem quadratic_normalized_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (η : ℝ) (_hη : 0 < η),
          ∃ Q : ℕ,
            20000 ≤ Q ∧
              ∀ (q : ℕ) [NeZero q] (_hq : Q ≤ q) (H : Subgroup (ZMod q)ˣ)
                (a b : DirichletCharacter ℂ q) (_hab : a ≠ b) (_ha : a ≠ a * b) (_hb : b ≠ a * b)
                (_hqa : a.IsQuadratic) (_hqb : b.IsQuadratic)
                (_hnp : ∀ χ ∈ NumberTheory.quadraticTriple a b, χ ≠ 1)
                (_haH : a ∈ NumberTheory.subgroupAnnihilator H)
                (_hbH : b ∈ NumberTheory.subgroupAnnihilator H) (wa wb wc X x : ℝ) (_hwa : 0 ≤ wa)
                (_hwb : 0 ≤ wb) (_hwc : 0 ≤ wc) (_hw : wa + wb + wc = 1) (_hx : 2 ≤ x)
                (T : Finset ℕ) (_hT : ∀ n ∈ T, (n : ℝ) ≤ X),
                let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
                let F := (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
                let E := η * Real.log q + C * (1 + Real.log q * Real.log x / Real.sqrt x)
                K.mass *
                            NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
                              (NumberTheory.quadraticTripleWeight a b wa wb wc) +
                          E -
                        P +
                      (1 - 2 * min wa (min wb wc)) * (F - P) <
                    0 →
                  ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤ X := by
  obtain ⟨C, hC, hb⟩ := weighted_least_prime_criterion K hg
  refine ⟨C, hC, fun η hη ↦ ?_⟩
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H a b hab ha hb' hqa hqb hnp haH hbH wa wb wc X x hwa hwb hwc hw hx T hT P F E hgap
  have hweight := (NumberTheory.quadraticTripleWeight_total a b hab ha hb' wa wb wc).trans hw
  apply
    hb q hq H (NumberTheory.quadraticTriple a b) (NumberTheory.quadraticTripleWeight a b wa wb wc)
      (fun χ _ ↦ NumberTheory.quadraticTripleWeight_nonneg a b hwa hwb hwc χ) hnp
      (NumberTheory.quadraticTriple_annihilates H a b haH hbH) (1 - 2 * min wa (min wb wc)) X x hx
      (quadratic_normalized_trace a b hab ha hb' hqa hqb hwa hwb hwc hw) T hT
  rw [hweight, mul_one]
  change
    K.mass *
          NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
            (NumberTheory.quadraticTripleWeight a b wa wb wc) +
        E <
      (1 + (1 - 2 * min wa (min wb wc))) * P - (1 - 2 * min wa (min wb wc)) * F
  nlinarith only [hgap]

/-- The actual full principal sum dominates every finite principal prefix.
Input: a nonzero ambient modulus, positive scale and arbitrary finite index set.
Claim: the omitted principal tail is nonnegative.
Proof: positivity of principal summands and absolute convergence.
Role: justify monotone trace penalties in endpoint reductions rather than assuming tail sign. -/
theorem principal_tail_nonneg (K : MellinKernel) {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 < x)
    (T : Finset ℕ) :
    0 ≤
      (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re -
        ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re :=
  let hs :=
    Complex.hasSum_re (MellinKernel.summable_summand K (1 : DirichletCharacter ℂ q) hx).hasSum
  sub_nonneg.mpr
    ((hs.summable.sum_le_tsum T
          (fun n _ ↦ MellinKernel.principal_summand_re_nonneg K hx n)).trans_eq
      hs.tsum_eq)

/-- Evaluate the quadratic endpoint reduction at an actual Mellin principal prefix and full sum.
Input: an admissible kernel, selected quadratic-family labels, normalized weights, scale and
finite prefix. Claim: a single or uniform endpoint has no larger actual deficit.
Proof: specialize the exact character-cost comparison to the actual principal data.
Role: connect the endpoint reduction to the least-prime comparison without sampled estimates. -/
theorem quadratic_prefix_endpoint (K : MellinKernel) {q : ℕ} (a b : DirichletCharacter ℂ q)
    (hab : a ≠ b) (ha : a ≠ a * b) (hb : b ≠ a * b) {wa wb wc : ℝ} (hwa : 0 ≤ wa) (hwb : 0 ≤ wb)
    (hwc : 0 ≤ wc) (hw : wa + wb + wc = 1) (x E : ℝ) (T : Finset ℕ) :
    let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let F := (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let ca := K.mass * Real.log a.conductor + E
    let cb := K.mass * Real.log b.conductor + E
    let cc := K.mass * Real.log (a * b).conductor + E
    min (min (ca - P + (F - P)) (cb - P + (F - P)))
        (min (cc - P + (F - P)) ((ca + cb + cc) / 3 - P + (F - P) / 3)) ≤
      K.mass *
              NumberTheory.weightedConductorLogSum (NumberTheory.quadraticTriple a b)
                (NumberTheory.quadraticTripleWeight a b wa wb wc) +
            E -
          P +
        (1 - 2 * min wa (min wb wc)) * (F - P) :=
  quadratic_character_deficit a b hab ha hb hwa hwb hwc hw K.mass
    (∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re)
    (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re E

end PseudoPrime.LLS.PaperStatements
