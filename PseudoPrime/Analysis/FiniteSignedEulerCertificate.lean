/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedResolventEulerBounds

/-! # Exact prefix certificates for nonnegative signed Euler weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Nonnegative running coefficients and decreasing nonnegative weights give a
nonnegative weighted sum with an initial coefficient. Induction consumes one
row at a time and moves the accumulated coefficient to the next weight. -/
private theorem finiteSigned_weighted_aux (l : List (ℚ × ℚ)) (w : ℚ → ℝ) (hw : Antitone w)
    (hw0 : ∀ a, 0 ≤ w a) (hsort : l.Pairwise (fun ab cd ↦ ab.1 ≤ cd.1)) (s b : ℝ) (hs : 0 ≤ s)
    (hb : 0 ≤ b) (hbound : ∀ ab ∈ l, w ab.1 ≤ b)
    (hpref : ∀ k, 0 ≤ s + (((l.take k).map Prod.snd).sum : ℝ)) :
    0 ≤ s * b + (l.map (fun ab ↦ (ab.2 : ℝ) * w ab.1)).sum := by
  induction l generalizing s b with
  | nil => simpa only [List.map_nil, List.sum_nil, add_zero] using mul_nonneg hs hb
  | cons ab rest ih =>
    have hsort' := List.pairwise_cons.mp hsort
    have hs' : 0 ≤ s + (ab.2 : ℝ) := by
      have h := hpref 1
      simpa only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, Rat.cast_add, Rat.cast_zero] using h
    have hpref' (k : ℕ) : 0 ≤ (s + (ab.2 : ℝ)) + (((rest.take k).map Prod.snd).sum : ℝ) := by
      have h := hpref (k + 1)
      simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, Rat.cast_add, add_assoc] using
        h
    have hbound' : ∀ cd ∈ rest, w cd.1 ≤ w ab.1 := by
      intro cd hcd
      exact hw (hsort'.1 cd hcd)
    have hi := ih hsort'.2 (s + ab.2) (w ab.1) hs' (hw0 ab.1) hbound' hpref'
    have hm := mul_nonneg hs (sub_nonneg.mpr (hbound ab (List.mem_cons_self ..)))
    simp only [List.map_cons, List.sum_cons]
    nlinarith only [hi, hm]

/-- Input: ordered rational nodes, nonnegative coefficient prefix sums,
and a nonnegative antitone real weight on the nodes.
Claim: the signed weighted combination is nonnegative.
Proof: use summation by parts while traversing the list.
Role: certify common Euler weights while allowing negative coefficients. -/
theorem finiteSigned_weighted_nonneg (l : List (ℚ × ℚ))
    (hsort : l.Pairwise (fun ab cd ↦ ab.1 ≤ cd.1))
    (hprefix : ∀ k, (0 : ℚ) ≤ ((l.take k).map Prod.snd).sum) (w : ℚ → ℝ) (hw : Antitone w)
    (hw0 : ∀ a, 0 ≤ w a) : 0 ≤ (l.map (fun ab ↦ (ab.2 : ℝ) * w ab.1)).sum := by
  cases l with
  | nil => simp only [List.map_nil, List.sum_nil, le_refl]
  | cons ab
    rest =>
    have hp (k : ℕ) : (0 : ℝ) ≤ ((((ab :: rest).take k).map Prod.snd).sum : ℝ) :=
      Rat.cast_nonneg.mpr (hprefix k)
    have hbound : ∀ cd ∈ ab :: rest, w cd.1 ≤ w ab.1 := by
      intro cd hcd
      rcases List.mem_cons.mp hcd with he | he
      · subst cd
        exact le_rfl
      · exact hw ((List.pairwise_cons.mp hsort).1 cd he)
    have h :=
      finiteSigned_weighted_aux (ab :: rest) w hw hw0 hsort 0 (w ab.1) le_rfl (hw0 ab.1) hbound
        (fun k ↦ by simpa only [zero_add] using hp k)
    simpa only [zero_mul, zero_add] using h

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Traverse the coefficient rows in order, checking each accumulated prefix. -/
def finiteSignedPrefixCheck (s : ℚ) : List (ℚ × ℚ) → Bool
  | [] => decide (0 ≤ s)
  | ab :: rest => decide (0 ≤ s) && finiteSignedPrefixCheck (s + ab.2) rest

/-- A successful sequential check bounds every coefficient prefix sum. -/
private theorem finiteSignedPrefixCheck_sound (l : List (ℚ × ℚ)) (s : ℚ)
    (h : finiteSignedPrefixCheck s l = true) (k : ℕ) : 0 ≤ s + ((l.take k).map Prod.snd).sum := by
  induction l generalizing s k with
  | nil =>
    simpa only [List.take_nil, List.map_nil, List.sum_nil, add_zero, finiteSignedPrefixCheck] using
      (of_decide_eq_true h : (0 : ℚ) ≤ s)
  | cons ab rest ih =>
    cases k with
    | zero =>
      have hs : (0 : ℚ) ≤ s := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
      simpa only [List.take_zero, List.map_nil, List.sum_nil, add_zero] using hs
    | succ k =>
      have hp := ih (s + ab.2) (Bool.and_eq_true_iff.mp h).2 k
      simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc] using hp

/-- Input: a finite rational node-coefficient list.
Output: true exactly when nodes are ordered and all rational coefficient prefixes are nonnegative.
Role: replace an infinite real-weight positivity premise by finite exact arithmetic. -/
def finiteSignedEulerCheck (l : List (ℚ × ℚ)) : Bool :=
  decide (l.Pairwise (fun ab cd ↦ ab.1 ≤ cd.1)) && finiteSignedPrefixCheck 0 l

/-- Input: the exact rational Euler check succeeds.
Claim: nodes are ordered and every coefficient prefix is nonnegative.
Proof: extract the Boolean conjunction and finite range checks.
Role: supply Abel's inequality with independently checked inputs. -/
theorem finiteSignedEulerCheck_sound (l : List (ℚ × ℚ)) (hc : finiteSignedEulerCheck l = true) :
    l.Pairwise (fun ab cd ↦ ab.1 ≤ cd.1) ∧ ∀ k, (0 : ℚ) ≤ ((l.take k).map Prod.snd).sum := by
  have h := Bool.and_eq_true_iff.mp hc
  refine ⟨of_decide_eq_true h.1, fun k ↦ ?_⟩
  simpa only [zero_add] using finiteSignedPrefixCheck_sound l 0 h.2 k

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
