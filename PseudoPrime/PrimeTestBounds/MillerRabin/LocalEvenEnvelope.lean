/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors

/-! # The finite local even-character witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The finite list of even correction anchors is nonempty. The explicit first
anchor supplies the inhabitant required by the finite minimum. -/
theorem localEvenAnchors_nonempty : localEvenAnchors.toFinset.Nonempty := by decide

/-- The minimum of the twenty certified squared local radii at logarithmic
scale `s`. Each radius is `max b (s - d)` for a listed anchor; the minimum
combines the corresponding actual witness bounds. -/
noncomputable def localEvenEnvelope (s : ℝ) : ℝ :=
  localEvenAnchors.toFinset.inf' localEvenAnchors_nonempty (fun x ↦ (max (x.1 : ℝ) (s - x.2.1)) ^ 2)

/-- The finite local envelope is continuous. Each squared maximum is continuous,
and the infimum is taken over a fixed nonempty finite set. -/
theorem localEvenEnvelope_continuous : Continuous localEvenEnvelope := by
  apply Continuous.finset_inf'_apply localEvenAnchors_nonempty
  intro x hx
  exact ((continuous_const.max (continuous_id.sub continuous_const)).pow 2)

/-- The finite local envelope is nondecreasing. Every anchor radius is positive
and nondecreasing, so its square and their finite minimum are nondecreasing. -/
theorem localEvenEnvelope_mono : Monotone localEvenEnvelope := by
  intro s t hst
  apply Finset.le_inf'
  intro ⟨b, d, j⟩ hm
  have hm' : (b, d, j) ∈ localEvenAnchors := List.mem_toFinset.mp hm
  have hc := (List.all_eq_true.mp localEvenAnchors_checked) (b, d, j) hm'
  have hbq : (8 : ℚ) ≤ b := (of_decide_eq_true hc).1
  have hb : (0 : ℝ) ≤ b := by exact_mod_cast (le_trans (by norm_num only : (0 : ℚ) ≤ 8) hbq)
  have hs : 0 ≤ max (b : ℝ) (s - d) := hb.trans (le_max_left _ _)
  have ht : 0 ≤ max (b : ℝ) (t - d) := hb.trans (le_max_left _ _)
  exact
    (Finset.inf'_le _ hm).trans ((sq_le_sq₀ hs ht).mpr (max_le_max_left _ (sub_le_sub_right hst _)))

/-- Under GRH, the finite local envelope bounds a prime rejecting odd `n > 1`
when its local passing residues lie in a proper subgroup at a divisor `q` and
`log q ≤ s`. A finite minimum is attained by an anchor, whose certified
correction supplies the rejecting prime. -/
theorem exists_prime_reject_local_envelope {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ localEvenEnvelope s ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨⟨b, d, j⟩, hm, heq⟩ :=
    Finset.exists_mem_eq_inf' localEvenAnchors_nonempty (fun x ↦ (max (x.1 : ℝ) (s - x.2.1)) ^ 2)
  have hm' : (b, d, j) ∈ localEvenAnchors := List.mem_toFinset.mp hm
  have hc := (List.all_eq_true.mp localEvenAnchors_checked) (b, d, j) hm'
  have hbq : (8 : ℚ) ≤ b := (of_decide_eq_true hc).1
  have hb : (8 : ℝ) ≤ b := by exact_mod_cast hbq
  rw [localEvenEnvelope, heq]
  exact exists_prime_reject_of_local_shift hn ho hqn H hH hpass hGRH hb (localEvenAnchor_lt hm') hs

end PseudoPrime.PrimeTestBounds.MillerRabin
