/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltSearch

/-! # Smallest-factor block of the uniform Korselt search -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- The kernel evaluates the bounded parameter enumeration in this block.
/-- The complete bounded parameter search with smallest factor below 20 has
exactly these four candidates. This checks the integer conditions directly. -/
theorem target030_candidates_below20 :
    target030CandidateRows 20 = [(7, 2, 18), (13, 2, 60), (13, 8, 36), (19, 14, 198)] := by
  decide +kernel

/-- A bounded uniform Korselt triple with ordered prime factors and smallest
factor below 20 belongs to one of four explicit products. The parameter list
is exhaustive, and exact division reconstructs the other factors. -/
theorem uniformKorselt_below20_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 20) :
    n = 8911 ∨ n = 29341 ∨ n = 314821 ∨ n = 1024651 := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ target030CandidateRows 20 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
  rw [target030_candidates_below20] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with h | h | h | h
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 19 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inl (by linarith only [hn, hrform])
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 61 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inr (Or.inr (Or.inl (by linarith only [hn, hrform])))
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 37 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inr (Or.inl (by linarith only [hn, hrform]))
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 199 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inr (Or.inr (Or.inr (by linarith only [hn, hrform])))

end PseudoPrime.PrimeTestBounds.MillerRabin
