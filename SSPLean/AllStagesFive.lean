import Mathlib.Tactic
import SSPLean.FiveStageWitness
import SSPLean.SixStageWitness

/-!
# Counterexamples at every stage count `≥ 5`

`SSPLean/FiveStageWitness.lean` refutes the algebraic-stability Claim at **five** stages
(`claim_is_false_five`), and `SSPLean/SixStageWitness.lean` develops padding by a zero-weight
stage for `WeakAlgStabData` — the Claim's hypotheses with its own weight condition `b ≥ 0`,
rather than the strict `b > 0` of `AlgStabData`.

This file combines them.  The padding machinery is generic in the stage count, so relabelling
the five-stage tableau by `perm5` and packaging it as a `StrictWeak 5` yields a witness at
*every* `s ≥ 5`.

As at six stages, the padded stages necessarily carry **zero** weight
(`SSPLean/SixStageWitness.lean`'s discussion: `R'e = b'` forces `r = 0`, and then
`bᵀ'c' = 1/2` forces `β = 0`), so the witnesses for `s > 5` satisfy the Claim as stated but do
not inhabit `AlgStabData`.
-/

open Finset

namespace SSP

namespace Counterexample

namespace Five

/-- **The five-stage tableau, as a `StrictWeak 5`.**  The abscissas are relabelled by `perm5`
so they increase in the index, and the strict bound `c < 1` is retained — it is what leaves
room for a padded stage. -/
theorem five_strictWeak_nonempty : Nonempty (StrictWeak 5) := by
  obtain ⟨t, htmem, hcub⟩ := tau5_cubic
  set r := Real.sqrt 5 with hrdef
  have hr2 : r^2 = 5 := sqrt5_sq
  have ht3 := cubic_reduce r t hr2 hcub
  have hrb := sqrt5_bracket
  have htb : t ∈ Set.Icc (35127/1000000 : ℝ) (35128/1000000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  have hvL : ∀ i ∈ range 5, vv5 r 0 i ≠ 0 := fun i hi =>
    (vv5_pos hrb (by norm_num) i hi).ne'
  have hvN : ∀ i ∈ range 5, vv5 r (-1/50) i ≠ 0 := fun i hi =>
    (vv5_pos hrb (by norm_num) i hi).ne'
  have hL : 0 < defu r t 0 := by
    unfold defu
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [bu_at_L r t hr2 ht3 i hi, cu_at_L r t hr2 ht3 hvL i hi])]
    rw [defect_L_eq r t hr2 ht3]
    exact dL_pos hrb htb
  have hN : defu r t (-1/50) < 0 := by
    unfold defu
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [bu_at_N r t hr2 ht3 i hi, cu_at_N r t hr2 ht3 hvN i hi])]
    rw [defect_N_eq r t hr2 ht3]
    exact dN_neg hrb htb
  obtain ⟨s, hs, h0⟩ := intermediate_value_Ioo (by norm_num : (-1/50 : ℝ) ≤ 0)
    (defu_cont hrb) (Set.mem_Ioo.2 ⟨hN, hL⟩)
  have hsIcc : s ∈ Set.Icc (-1/50 : ℝ) 0 :=
    Set.mem_Icc.2 ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩ :=
    five_uniform hr2 ht3 hrb htb hsIcc
  have hv : ∀ i ∈ range 5, vv5 r s i ≠ 0 := fun i hi => (vv5_pos hrb hsIcc i hi).ne'
  refine ⟨{
    data :=
      { A := Ap5 r t s
        b := bp5 r t s
        R := Rp5 r t s
        c := cp5 r t s
        hA := Ap5_nonneg_all hrb htb hsIcc
        hb := fun i hi => (q2 (perm5 i) (perm5_mem i hi)).le
        hc := fun i hi => by
          rw [Ap5_rowsum]; exact q3 (perm5 i) (perm5_mem i hi)
        hcmono := q5
        hcrange := fun i hi =>
          ⟨le_of_lt (q4 (perm5 i) (perm5_mem i hi)).1,
           le_of_lt (q4 (perm5 i) (perm5_mem i hi)).2⟩
        hRsymm := fun i hi j hj => q6 (perm5 i) (perm5_mem i hi) (perm5 j) (perm5_mem j hj)
        hRpsd := by
          intro x
          have h : ∑ i ∈ range 5, ∑ j ∈ range 5, Rp5 r t s i j * (x i * x j)
              = ∑ i ∈ range 5, ∑ j ∈ range 5,
                  Ru r t s i j * ((fun k => x (iperm5 k)) i * (fun k => x (iperm5 k)) j) := by
            rw [← sum_perm5_2 (fun i j => Ru r t s i j * (x (iperm5 i) * x (iperm5 j)))]
            refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
            unfold Rp5
            rw [iperm5_perm5 i hi, iperm5_perm5 j hj]
          rw [h]; exact q7 _
        hRe := fun i hi => by
          rw [Rp5_rowsum]; exact (q8 (perm5 i) (perm5_mem i hi)).symm
        h1 := by rw [show ∑ i ∈ range 5, bp5 r t s i = ∑ i ∈ range 5, bu r t s i from
                       sum_perm5 (fun i => bu r t s i)]; exact q9
        h2 := by
          rw [show ∑ i ∈ range 5, bp5 r t s i * cp5 r t s i
                 = ∑ i ∈ range 5, bu r t s i * cu r t s i from
               sum_perm5 (fun i => bu r t s i * cu r t s i)]
          exact q10
        h3 := by
          have inner : ∀ i, ∑ j ∈ range 5, Ap5 r t s i j * cp5 r t s j
              = ∑ j ∈ range 5, Au r t s (perm5 i) j * cu r t s j := fun i =>
            sum_perm5 (fun j => Au r t s (perm5 i) j * cu r t s j)
          calc ∑ i ∈ range 5, bp5 r t s i * ∑ j ∈ range 5, Ap5 r t s i j * cp5 r t s j
              = ∑ i ∈ range 5, bu r t s (perm5 i)
                  * ∑ j ∈ range 5, Au r t s (perm5 i) j * cu r t s j := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [inner i]; rfl
            _ = ∑ i ∈ range 5, bu r t s i * ∑ j ∈ range 5, Au r t s i j * cu r t s j :=
                sum_perm5 (fun i => bu r t s i * ∑ j ∈ range 5, Au r t s i j * cu r t s j)
            _ = 1/6 := q11
        h4 := by
          rw [show ∑ i ∈ range 5, bp5 r t s i * (cp5 r t s i)^2
                 = ∑ i ∈ range 5, bu r t s i * (cu r t s i)^2 from
               sum_perm5 (fun i => bu r t s i * (cu r t s i)^2)]
          unfold defu at h0; linarith
        hM := fun i hi j hj => by
          rw [Mp5_inner, Mp5_inner]
          exact q12 (perm5 i) (perm5_mem i hi) (perm5 j) (perm5_mem j hj) }
    hlt1 := fun i hi => (q4 (perm5 i) (perm5_mem i hi)).2 }⟩

/-- **The Claim fails at every stage count `≥ 5`.**

For each `s ≥ 5` there is an `s`-stage tableau satisfying every hypothesis of the Claim ---
with the Claim's own weight condition `b ≥ 0` --- while `M = R A + Aᵀ R − b bᵀ = 0`.  The
witnesses for `s > 5` carry `s − 5` stages of zero weight, which by the forcing argument of
`SSPLean/SixStageWitness.lean` no padding argument can avoid. -/
theorem weak_counterexample_of_ge_five {s : ℕ} (hs : 5 ≤ s) :
    Nonempty (WeakAlgStabData s) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨w⟩ := five_strictWeak_nonempty
  obtain ⟨wn⟩ := w.exists_all n
  exact ⟨wn.data⟩

/-- **The Claim is false at every stage count `≥ 5`**, with the algebraic-stability matrix
exhibited as positive semidefinite. -/
theorem claim_false_all_stages_five {s : ℕ} (hs : 5 ≤ s) :
    ∃ d : WeakAlgStabData s, PSDOn s (fun i j =>
      (∑ k ∈ range s, d.R i k * d.A k j)
        + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) := by
  obtain ⟨d⟩ := weak_counterexample_of_ge_five hs
  exact ⟨d, d.M_psd⟩

end Five

end Counterexample

end SSP
