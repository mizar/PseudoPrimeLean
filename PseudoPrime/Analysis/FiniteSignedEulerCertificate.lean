/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedResolventEulerBounds
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.List.GetD

/-! # Exact prefix certificates for nonnegative signed Euler weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a finite list, a default value and a real-valued map.
Claim: the mapped list sum equals the indexed sum through the list length.
Proof: use the finite enumeration and the in-range default lookup identity.
Role: apply Abel's inequality to rational node lists. -/
theorem sum_map_eq_sum_range_getD {α : Type*} (l : List α) (d : α) (f : α → ℝ) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
  have he : (fun i : Fin l.length ↦ f (l.get i)) = (fun i : Fin l.length ↦ f (l.getD i d)) := by
    apply funext
    intro i
    rw [List.getD_eq_getElem l d i.isLt]
    rfl
  calc
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
      rw [← List.sum_ofFn]
      change (l.map f).sum = (List.ofFn (f ∘ l.get)).sum
      rw [← List.map_ofFn, List.ofFn_get]
    _ = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
      rw [he]
      exact Fin.sum_univ_eq_sum_range (fun i ↦ f (l.getD i d)) l.length

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: ordered rational nodes, nonnegative coefficient prefix sums,
and a nonnegative antitone real weight on the nodes.
Claim: the signed weighted combination is nonnegative.
Proof: apply Abel's one-sided lower inequality after casting rational prefixes.
Role: certify common Euler weights while allowing negative coefficients. -/
theorem finiteSigned_weighted_nonneg (l : List (ℚ × ℚ))
    (hsort : l.Pairwise (fun ab cd ↦ ab.1 ≤ cd.1))
    (hprefix : ∀ k ≤ l.length, (0 : ℚ) ≤ ∑ i ∈ Finset.range k, (l.getD i (0, 0)).2) (w : ℚ → ℝ)
    (hw : Antitone w) (hw0 : ∀ a, 0 ≤ w a) : 0 ≤ (l.map (fun ab ↦ (ab.2 : ℝ) * w ab.1)).sum := by
  have hp (k : ℕ) (hk : k ≤ l.length) :
    (0 : ℝ) ≤ ∑ i ∈ Finset.range k, ((l.getD i (0, 0)).2 : ℝ) := by exact_mod_cast hprefix k hk
  have hanti : AntitoneOn (fun i ↦ w (l.getD i (0, 0)).1) (Set.Iio l.length) := by
    intro i hi j hj hij
    change w (l.getD j (0, 0)).1 ≤ w (l.getD i (0, 0)).1
    rw [List.getD_eq_getElem l (0, 0) hi, List.getD_eq_getElem l (0, 0) hj]
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact hw (List.pairwise_iff_getElem.mp hsort i j hi hj hlt)
    · exact le_rfl
  have ha := Finset.mul_le_sum_mul_of_le_sum_range hp (fun i ↦ hw0 (l.getD i (0, 0)).1) hanti
  rw [sum_map_eq_sum_range_getD l (0, 0)]
  rw [zero_mul] at ha
  exact ha

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a finite rational node-coefficient list.
Output: true exactly when nodes are ordered and all rational coefficient prefixes are nonnegative.
Role: replace an infinite real-weight positivity premise by finite exact arithmetic. -/
def finiteSignedEulerCheck (l : List (ℚ × ℚ)) : Bool :=
  decide (l.Pairwise (fun ab cd ↦ ab.1 ≤ cd.1)) &&
    (List.range (l.length + 1)).all
      (fun k ↦ decide ((0 : ℚ) ≤ ∑ i ∈ Finset.range k, (l.getD i (0, 0)).2))

/-- Input: the exact rational Euler check succeeds.
Claim: nodes are ordered and every coefficient prefix is nonnegative.
Proof: extract the Boolean conjunction and finite range checks.
Role: supply Abel's inequality with independently checked inputs. -/
theorem finiteSignedEulerCheck_sound (l : List (ℚ × ℚ)) (hc : finiteSignedEulerCheck l = true) :
    l.Pairwise (fun ab cd ↦ ab.1 ≤ cd.1) ∧
      ∀ k ≤ l.length, (0 : ℚ) ≤ ∑ i ∈ Finset.range k, (l.getD i (0, 0)).2 := by
  have h := Bool.and_eq_true_iff.mp hc
  refine ⟨of_decide_eq_true h.1, fun k hk ↦ ?_⟩
  exact of_decide_eq_true (List.all_eq_true.mp h.2 k (List.mem_range.mpr (Nat.lt_succ_of_le hk)))

/-- Input: the exact rational Euler check and a real base at least one.
Claim: the combined Euler weight is nonnegative at that base.
Proof: real powers are nonnegative and antitone in the ordered nodes; apply Abel's inequality.
Role: certify positivity simultaneously on the whole halfline. -/
theorem finiteSignedEulerWeight_nonneg_of_check (l : List (ℚ × ℚ))
    (hc : finiteSignedEulerCheck l = true) {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ finiteSignedEulerWeight l u := by
  have h := finiteSignedEulerCheck_sound l hc
  dsimp only [finiteSignedEulerWeight]
  apply finiteSigned_weighted_nonneg l h.1 h.2 (fun a : ℚ ↦ u ^ (-(1 / 2 + (a : ℝ))))
  · intro a b hab
    exact Real.rpow_le_rpow_of_exponent_le hu (neg_le_neg (add_le_add le_rfl (Rat.cast_le.mpr hab)))
  · intro a
    exact Real.rpow_nonneg (zero_le_one.trans hu) _

/-- Input: the exact rational Euler check and a natural index.
Claim: the combined Mangoldt weight is nonnegative.
Proof: combine the Euler halfline result with von Mangoldt nonnegativity.
Role: discharge the nonnegative paired-tail premise in spectral estimates. -/
theorem finiteSignedMangoldtWeight_nonneg_of_check (l : List (ℚ × ℚ))
    (hc : finiteSignedEulerCheck l = true) (n : ℕ) : 0 ≤ finiteSignedMangoldtWeight l n := by
  exact
    finiteSignedMangoldtWeight_nonneg l (fun _ hu ↦ finiteSignedEulerWeight_nonneg_of_check l hc hu)
      n

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: rational node-coefficient pairs.
Output: true when every node exceeds one half and the exact Euler check succeeds.
Role: combine convergence and whole-halfline positivity into one finite certificate. -/
def finiteSignedPhaseNodeCheck (l : List (ℚ × ℚ)) : Bool :=
  l.all (fun ab ↦ decide ((1 / 2 : ℚ) < ab.1)) && finiteSignedEulerCheck l

/-- Input: the combined node check succeeds.
Claim: every node exceeds one half and the Euler positivity check succeeds.
Proof: extract the finite Boolean tests. Role: feed the phase-resolvent comparison. -/
theorem finiteSignedPhaseNodeCheck_sound (l : List (ℚ × ℚ))
    (hc : finiteSignedPhaseNodeCheck l = true) :
    (∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) ∧ finiteSignedEulerCheck l = true := by
  have h := Bool.and_eq_true_iff.mp hc
  exact ⟨fun ab hab ↦ of_decide_eq_true (List.all_eq_true.mp h.1 ab hab), h.2⟩

end PseudoPrime.Analysis
