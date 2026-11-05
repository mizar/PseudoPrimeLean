/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenLogEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalAdaptiveMonotone
public import PseudoPrime.LLS.AdaptiveReciprocalWitnessBounds

/-! # Local adaptive and even-character witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a proper local subgroup at modulus at least 600 that contains
all passing residues gives an original-input rejecting prime within the adaptive
radius at that modulus. A prime outside the subgroup cannot pass by containment.
This supplies the adaptive candidate for the local witness envelope. -/
theorem exists_prime_reject_local_adaptive {n q : ℕ} [NeZero q] (hq : 600 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (Real.log q)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hout⟩ := LLS.exists_prime_outside_adaptivePart2_GRH hq H hH hGRH
  exact ⟨p, hp, hb, fun hpasse ↦ hout (hpass p hpasse)⟩

/-- Under GRH, for odd `n > 1` and a proper local subgroup at a divisor
`q ≥ 600`, a rejecting prime lies below the minimum of the adaptive bound at
`q`, the squared scale, and the finite even envelope at scale `s ≥ log q`.
Select the smaller actual witness bound; the full scale-only envelope still
requires monotonicity of the adaptive radius. -/
theorem exists_prime_reject_local_adaptive_min {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hq : 600 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          min ((Analysis.adaptivePart2CutoffRoot (Real.log q)) ^ 2)
            (min (s ^ 2) (localEvenEnvelope s)) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h :
    (Analysis.adaptivePart2CutoffRoot (Real.log q)) ^ 2 ≤ min (s ^ 2) (localEvenEnvelope s)
  · obtain ⟨p, hp, hb, hout⟩ := LLS.exists_prime_outside_adaptivePart2_GRH hq H hH hGRH
    refine ⟨p, hp, ?_, fun hpasse ↦ hout (hpass p hpasse)⟩
    rw [min_eq_left h]
    exact hb
  · obtain ⟨p, hp, hb, hf⟩ :=
      exists_prime_reject_local_log_min hn ho ((by decide : 5 ≤ 600).trans hq) hqn H hH hpass hGRH
        hs
    refine ⟨p, hp, ?_, hf⟩
    rw [min_eq_right (le_of_not_ge h)]
    exact hb

/-- Under the local adaptive witness hypotheses and `7 ≤ log q ≤ s`, replace
the modulus-dependent adaptive radius by its value at the common scale `s`.
Monotonicity and positivity preserve the squared bound. This connects the
adaptive, logarithmic and even candidates at one scale. -/
theorem exists_prime_reject_local_scale_min {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hq : 600 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hlo : 7 ≤ Real.log q)
    (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          min ((Analysis.adaptivePart2CutoffRoot s) ^ 2) (min (s ^ 2) (localEvenEnvelope s)) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hfr :=
    Analysis.finerPart2Root_ge_36_5_of_639_100_le (L := Real.log q) (by linarith only [hlo])
  have hroot := (Analysis.adaptivePart2Root_height_and_cutoff hfr).1
  have hm := adaptive_local_radius_mono hlo hs
  have hsqr :
    (Analysis.adaptivePart2CutoffRoot (Real.log q)) ^ 2 ≤
      (Analysis.adaptivePart2CutoffRoot s) ^ 2 :=
    (sq_le_sq₀ (by linarith only [hroot]) (by linarith only [hroot, hm])).mpr hm
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_local_adaptive_min hn ho hq hqn H hH hpass hGRH hs
  exact ⟨p, hp, hb.trans (min_le_min_right _ hsqr), hf⟩

/-- The adaptive radius at `max 7 s` is at least seven for every real `s`.
The existing height estimate applies at the clamped logarithmic scale. This
keeps the adaptive candidate above the small-modulus logarithmic bound. -/
theorem adaptive_clamped_radius_ge_seven (s : ℝ) :
    7 ≤ Analysis.adaptivePart2CutoffRoot (max 7 s) := by
  have hlevel : 7 ≤ max 7 s := le_max_left _ _
  have hfr :=
    Analysis.finerPart2Root_ge_36_5_of_639_100_le (L := max 7 s) (by linarith only [hlevel])
  exact (Analysis.adaptivePart2Root_height_and_cutoff hfr).1

/-- A modulus at least five with logarithm at least seven is at least 600.
The certified upper bound for `log 2` gives `log 600 < 7`; monotonicity of
the logarithm then proves the entrance for the adaptive witness theorem. -/
theorem six_hundred_le_of_log_seven {q : ℕ} (hq : 5 ≤ q) (hlarge : 7 ≤ Real.log q) : 600 ≤ q := by
  have hlog600 : Real.log (600 : ℝ) < 7 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 600) (by norm_num only : (600 : ℝ) ≤ 2 ^ 10)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  by_contra hnq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by decide : 1 ≤ 5) hq)
  have hq' : (q : ℝ) ≤ 600 := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hnq))
  have h := Real.log_le_log (by linarith only [hqR] : (0 : ℝ) < q) hq'
  linarith only [h, hlog600, hlarge]

/-- For a modulus at least five with logarithm below seven, its logarithm
square is at most the clamped adaptive radius squared at every scale. Both
terms are nonnegative and the latter radius is at least seven. This covers the
small-modulus branch of the common adaptive candidate. -/
theorem local_small_log_sq_le_adaptive {q : ℕ} (hq : 5 ≤ q) (hsmall : Real.log q < 7) (s : ℝ) :
    (Real.log q) ^ 2 ≤ (Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by decide : 1 ≤ 5) hq)
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hroot := adaptive_clamped_radius_ge_seven s
  nlinarith only [hlog0, hsmall, hroot, sq_nonneg (7 - Real.log q)]

/-- Under GRH, a proper local subgroup at any divisor `q ≥ 5` containing all
strong passes gives an original-input rejecting prime bounded by the minimum
of the clamped adaptive square, `s²`, and the finite even envelope, provided
`log q ≤ s`. Large local levels use adaptive monotonicity; small levels use the
log-square witness and the clamped radius floor. This combines three candidates
at a common scale for every admissible local modulus. -/
theorem exists_prime_reject_local_clamped_min {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hq : 5 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ} (hs : Real.log q ≤ s) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          min ((Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2)
            (min (s ^ 2) (localEvenEnvelope s)) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hlarge : 7 ≤ Real.log q
  · rw [max_eq_right (hlarge.trans hs)]
    exact
      exists_prime_reject_local_scale_min hn ho (six_hundred_le_of_log_seven hq hlarge) hqn H hH
        hpass hGRH hlarge hs
  · by_cases h :
      (Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2 ≤ min (s ^ 2) (localEvenEnvelope s)
    · obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_local_log_sq hn ho hq hqn H hH hpass hGRH
      refine ⟨p, hp, ?_, hf⟩
      rw [min_eq_left h]
      exact hb.trans (local_small_log_sq_le_adaptive hq (lt_of_not_ge hlarge) s)
    · obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_local_log_min hn ho hq hqn H hH hpass hGRH hs
      refine ⟨p, hp, ?_, hf⟩
      rw [min_eq_right (le_of_not_ge h)]
      exact hb

end PseudoPrime.PrimeTestBounds.MillerRabin
