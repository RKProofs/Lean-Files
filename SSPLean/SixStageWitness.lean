import Mathlib
import SSPLean.AlgStabCounterexample
set_option linter.style.setOption false

/-!
# A six-stage counterexample with a cubic parameter

`SSPLean/AlgStabCounterexample.lean` refutes the algebraic-stability Claim of `main-4.tex`
*conditionally* on an inhabitant of `ConstructionData` / `ConstructionFamily`;
`SSPLean/NineStageWitness.lean` supplies ten of the eleven conditions at a rational
parameter.  This file gives a **smaller** construction whose only irrationality is a root
of an explicit rational **cubic**, and verifies the algebraic core of it.

## The construction

Let `s = 6`, let `P` be the cyclic shift on `range 6`, and put

  `G = (1/4) P + τ P²`,   where  `192 τ³ + 96 τ² − 1 = 0`,  `τ ∈ (0, 1/4)`.

With `D = diag v` for `v > 0`, set `A = D⁻¹ G D`, `b = D h`, `R = D X D`.  Then `A ≥ 0`
automatically (`G ≥ 0`, `v > 0`), and both

  `R A + Aᵀ R = b bᵀ`   and   `R e = b`

follow from the two identities

  `X G + Gᵀ X = h hᵀ`,      `X v = h`.                                    (★)

The circulant `G` preserves the **rational** three-dimensional subspace
`V = span(e, x, y)` with `x = (2,1,−1,−2,−1,1)`, `y = (0,1,1,0,−1,−1)`, on which
`P x = x/2 − 3y/2`, `P y = x/2 + y/2`.  Taking `X = B S Bᵀ` with `B = [e|x|y]` reduces (★)
to a `3 × 3` system, and two of the four order conditions become *identities*:

  `m₁ = m₀²/2`,     `m₀ = 2 tr Γ = 6g₀ + 4g₁`,

so `g₀ = 0`, `g₁ = 1/4` yields `bᵀe = 1` and `bᵀc = 1/2` for free.  The condition
`bᵀAc = 1/6` depends only on `g` and pins `τ` — it *is* the cubic above.  Only
`bᵀc² = 1/3` remains, and it comes from the intermediate value theorem along the rational
line `v(s) = (21/8 − s, 17/4 + 2s, 17/4 − 2s, 7/4 + s, 1, 3/2)`.  Along that line the
direction `(−1,2,−2,1,0,0)` lies in `ker Bᵀ`, so `z = Bᵀv(s)` is constant and hence
`S`, `h`, `X` are constant: only `D` moves.

## What is proved here

* `tau_exists` — the parameter `τ` exists in the tight bracket `(9366/10⁵, 9367/10⁵)`.
* `XGid_i_j` (21 lemmas) and `XG_add_GtX` — the identity `X G + Gᵀ X = h hᵀ`, entrywise
  and in matrix form.  Each entry's raw polynomial in `t` is exactly divisible by the
  cubic, and the quotient is handed to `linear_combination` as a certificate.
* `Xv_eq_h` — the identity `X v(σ) = h`, for **every** `σ` (pure `ring`; no cubic needed).
* `Am_nonneg`, `Am_nonneg_all` — `A ≥ 0` entrywise (the latter globally, as
  `AlgStabData.hA` demands).
* `bvec_pos` — `b > 0` on the stage range.
* `cvec_eq_rowsum` — `c = A e`.
* `cvec_mem` — the abscissas lie strictly inside `(0,1)`.
* `cvec_sorted`, `cvec_perm_mono` — the abscissas are strictly ordered by the *fixed*
  permutation `(3,1,2,4,5,0)`, hence pairwise distinct, and increasing in the index after
  relabelling by `perm`.
* `Sm_psd`, `Xm_quadform`, `Xm_psd`, `Rm_psd` — positive semidefiniteness of `R`, via
  `X = B S Bᵀ` and an explicit completion of squares for the `3 × 3` matrix `S` whose
  leading principal minors `sm1`, `sm2`, `sm3` are positive on the bracket.
* `Rm_symm`, `Rm_rowsum` — `R` symmetric with `R e = b`.
* `Mm_zero` — **`M = R A + Aᵀ R − b bᵀ = 0`**, transported from `X G + Gᵀ X = h hᵀ` by
  conjugation with `D = diag v`.
* `uniform_conditions` — the ten conditions above, packaged, holding for *every* `t` in
  the bracket satisfying the cubic and *every* `σ ∈ [1/2, 3/4]`.
* `defectL_neg_of_mem`, `defectR_pos_of_mem`, `defect_sign_change` — the order-three
  defect has strictly opposite signs at `σ = 1/2` and `σ = 3/4`, decided from the rational
  bracket on `τ` alone.
* `six_stage_defect_root` — hence a parameter `σ* ∈ (1/2, 3/4)` at which `bᵀc² = 1/3`.

## The main result

`claim_is_false` — **unconditional**: there exist a cubic parameter `t` and a line
parameter `s` for which the tableau satisfies every hypothesis of the Claim (including all
four order conditions) while `M = 0`.  Nothing is assumed; `τ` comes from `tau_exists` and
`s` from `defect_has_root`.

Supporting results, all uniform in the parameters:
`Am_nonneg`/`Am_nonneg_all`, `bvec_pos`, `cvec_eq_rowsum`, `cvec_mem`, `cvec_sorted`,
`cvec_perm_mono`, `Rm_symm`, `Rm_rowsum`, `Rm_psd` (via `Sm_psd`, `Xm_quadform`, `Xm_psd`
and the minors `sm1`,`sm2`,`sm3`), `Mm_zero`, packaged as `uniform_conditions`;
the order conditions `m0_gen`, `m1_gen`, `m2_gen`; the defect identification
`defectL_eq`, `defectR_eq`; continuity `defect_cont`; and the sign change
`defectL_neg_of_mem`, `defectR_pos_of_mem`.

The one earlier gap — that `defectL`/`defectR` are the defect *of this tableau* — is now
closed by `defectL_eq` / `defectR_eq`, so `defect_has_root` is about the tableau itself and
not about an assumed interpolant.

`algStabData_six_nonempty` — **`AlgStabData 6` is inhabited**, landing the counterexample in
the framework of `SSPLean/AlgStabCounterexample.lean`.  The tableau is relabelled by `perm`
(so that `c` increases in the index, as that structure requires) and each field is
transferred by the reindexing lemmas `sum_perm`, `sum_perm2`.  Two consequences become
unconditional: `exists_psd_M` (the algebraic-stability matrix of a genuine counterexample is
positive semidefinite — the configuration the Claim declares impossible) and
`exists_nondiagonal_certificate` (via `R_not_diagonal`: the certificate is necessarily
non-diagonal, so the counterexample is consistent with the diagonal-`R` barrier of
`SSPLean/BStability.lean` rather than contradicting it).

## Conventions

As in `SSPLean/BStability.lean`, matrices are `ℕ → ℕ → ℝ` and sums run over
`Finset.range s`.
-/

open Finset

namespace SSP

namespace Counterexample

/-! ## Padding: the Claim's own weight hypothesis `b ≥ 0`

`AlgStabData` requires `b > 0` strictly, which is *stronger* than the Claim's own `b ≥ 0`.
The distinction matters here: appending a stage of **zero** weight preserves every condition,
so a witness at `s` stages yields one at every larger stage count — but the padded stage has
weight `0`, so the result witnesses the Claim as stated rather than inhabiting `AlgStabData`.

The zero weight is forced, not chosen.  Block `(1,1)` of `M' = 0` gives `2(r·x)(w·x) = 0` for
all `x`, and `R' e = b'` reads `R e + r = b`, so `r = 0` since `R e = b` already.  Then
`R u = β b` together with `R e = b` gives `b·u = e·(R u) = β`, while `α = β/2`, so
`bᵀ'c' = 1/2` becomes `1/2 + β + β²/2 = 1/2`; hence `β = 0` (the other root `β = −2` violates
`b ≥ 0`).  No padding argument can therefore produce strictly positive weights — that needs a
genuinely different construction at each stage count. -/

/-- The hypotheses of the Claim with its *own* weight condition `b ≥ 0`, rather than the
strict `b > 0` of `AlgStabData`.  This is the form in which the Claim is stated, and it is
the form closed under appending a zero-weight stage. -/
structure WeakAlgStabData (s : ℕ) where
  /-- Coefficient matrix. -/
  A : ℕ → ℕ → ℝ
  /-- Weights. -/
  b : ℕ → ℝ
  /-- Certificate. -/
  R : ℕ → ℕ → ℝ
  /-- Abscissas. -/
  c : ℕ → ℝ
  /-- nonnegativity of `A`. -/
  hA : ∀ i j, 0 ≤ A i j
  /-- `b ≥ 0` — the Claim's own hypothesis. -/
  hb : ∀ i ∈ range s, 0 ≤ b i
  /-- `c = A e`. -/
  hc : ∀ i ∈ range s, c i = ∑ j ∈ range s, A i j
  /-- strictly increasing abscissas. -/
  hcmono : ∀ i ∈ range s, ∀ j ∈ range s, i < j → c i < c j
  /-- abscissas in `[0,1]`. -/
  hcrange : ∀ i ∈ range s, 0 ≤ c i ∧ c i ≤ 1
  /-- symmetry of `R`. -/
  hRsymm : SymmOn s R
  /-- positive semidefiniteness of `R`. -/
  hRpsd : PSDOn s R
  /-- `R e = b`. -/
  hRe : ∀ i ∈ range s, b i = ∑ j ∈ range s, R i j
  /-- `bᵀe = 1`. -/
  h1 : ∑ i ∈ range s, b i = 1
  /-- `bᵀc = 1/2`. -/
  h2 : ∑ i ∈ range s, b i * c i = 1 / 2
  /-- `bᵀAc = 1/6`. -/
  h3 : ∑ i ∈ range s, b i * ∑ j ∈ range s, A i j * c j = 1 / 6
  /-- `bᵀc² = 1/3`. -/
  h4 : ∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3
  /-- `M = R A + Aᵀ R − b bᵀ = 0`. -/
  hM : ∀ i ∈ range s, ∀ j ∈ range s,
    (∑ k ∈ range s, R i k * A k j) + (∑ k ∈ range s, R j k * A k i) - b i * b j = 0

variable {s : ℕ}

noncomputable def padA (A : ℕ → ℕ → ℝ) (α : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  if i < s then (if j < s then A i j else 0) else (if j = s then α else 0)
noncomputable def padb (b : ℕ → ℝ) : ℕ → ℝ := fun i => if i < s then b i else 0
noncomputable def padR (R : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i j =>
  if i < s then (if j < s then R i j else 0) else 0
noncomputable def padc (c : ℕ → ℝ) (α : ℝ) : ℕ → ℝ := fun i => if i < s then c i else α

@[simp] lemma padb_lt {b : ℕ → ℝ} {i : ℕ} (h : i < s) : padb (s := s) b i = b i := by
  simp [padb, h]
@[simp] lemma padb_self {b : ℕ → ℝ} : padb (s := s) b s = 0 := by simp [padb]
@[simp] lemma padc_lt {c : ℕ → ℝ} {α : ℝ} {i : ℕ} (h : i < s) : padc (s := s) c α i = c i := by
  simp [padc, h]
@[simp] lemma padc_self {c : ℕ → ℝ} {α : ℝ} : padc (s := s) c α s = α := by simp [padc]
@[simp] lemma padA_lt {A : ℕ → ℕ → ℝ} {α : ℝ} {i j : ℕ} (hi : i < s) (hj : j < s) :
    padA (s := s) A α i j = A i j := by simp [padA, hi, hj]
@[simp] lemma padA_lt_hi {A : ℕ → ℕ → ℝ} {α : ℝ} {i : ℕ} (hi : i < s) :
    padA (s := s) A α i s = 0 := by simp [padA, hi]
@[simp] lemma padA_self {A : ℕ → ℕ → ℝ} {α : ℝ} : padA (s := s) A α s s = α := by
  simp [padA]
@[simp] lemma padA_self_lt {A : ℕ → ℕ → ℝ} {α : ℝ} {j : ℕ} (hj : j < s) :
    padA (s := s) A α s j = 0 := by
  simp [padA, Nat.ne_of_lt hj]
@[simp] lemma padR_lt {R : ℕ → ℕ → ℝ} {i j : ℕ} (hi : i < s) (hj : j < s) :
    padR (s := s) R i j = R i j := by simp [padR, hi, hj]
@[simp] lemma padR_hi {R : ℕ → ℕ → ℝ} {i : ℕ} (hi : i < s) : padR (s := s) R i s = 0 := by
  simp [padR, hi]
@[simp] lemma padR_self {R : ℕ → ℕ → ℝ} {j : ℕ} : padR (s := s) R s j = 0 := by simp [padR]



/-- **Padding by a zero-weight stage.** -/
noncomputable def WeakAlgStabData.pad (d : WeakAlgStabData s) {α : ℝ}
    (hα : ∀ i ∈ range s, d.c i < α) (hα1 : α ≤ 1) (hα0 : 0 ≤ α) :
    WeakAlgStabData (s+1) where
  A := padA (s := s) d.A α
  b := padb (s := s) d.b
  R := padR (s := s) d.R
  c := padc (s := s) d.c α
  hA := by
    intro i j
    by_cases hi : i < s
    · by_cases hj : j < s
      · rw [padA_lt hi hj]; exact d.hA i j
      · simp only [padA, if_pos hi, if_neg hj]; exact le_refl 0
    · simp only [padA, if_neg hi]
      split <;> [exact hα0; exact le_refl 0]
  hb := by
    intro i hi
    by_cases h : i < s
    · rw [padb_lt h]; exact d.hb i (mem_range.2 h)
    · simp only [padb, if_neg h]; exact le_refl 0
  hc := by
    intro i hi
    have hi' := mem_range.1 hi
    by_cases h : i < s
    · rw [padc_lt h, Finset.sum_range_succ, padA_lt_hi h, add_zero]
      rw [d.hc i (mem_range.2 h)]
      exact Finset.sum_congr rfl fun j hj => (padA_lt h (mem_range.1 hj)).symm
    · have hs : i = s := by omega
      rw [hs, padc_self, Finset.sum_range_succ, padA_self]
      have hz : ∑ j ∈ range s, padA (s := s) d.A α s j = 0 :=
        Finset.sum_eq_zero fun j hj => padA_self_lt (mem_range.1 hj)
      rw [hz, zero_add]
  hcmono := by
    intro i hi j hj hij
    have hj' := mem_range.1 hj
    by_cases h : j < s
    · rw [padc_lt (lt_trans hij h), padc_lt h]
      exact d.hcmono i (mem_range.2 (lt_trans hij h)) j (mem_range.2 h) hij
    · have hjs : j = s := by omega
      rw [hjs, padc_self, padc_lt (by omega : i < s)]
      exact hα i (mem_range.2 (by omega))
  hcrange := by
    intro i hi
    by_cases h : i < s
    · rw [padc_lt h]; exact d.hcrange i (mem_range.2 h)
    · have hs : i = s := by have := mem_range.1 hi; omega
      rw [hs, padc_self]; exact ⟨hα0, hα1⟩
  hRsymm := by
    intro i hi j hj
    by_cases h1 : i < s
    · by_cases h2 : j < s
      · rw [padR_lt h1 h2, padR_lt h2 h1]; exact d.hRsymm i (mem_range.2 h1) j (mem_range.2 h2)
      · have hjs : j = s := by have := mem_range.1 hj; omega
        rw [hjs, padR_hi h1, padR_self]
    · have hs : i = s := by have := mem_range.1 hi; omega
      rw [hs, padR_self]
      by_cases h2 : j < s
      · rw [padR_hi h2]
      · have hjs : j = s := by have := mem_range.1 hj; omega
        rw [hjs, padR_self]
  hRpsd := by
    intro x
    have h : ∑ i ∈ range (s+1), ∑ j ∈ range (s+1), padR (s := s) d.R i j * (x i * x j)
        = ∑ i ∈ range s, ∑ j ∈ range s, d.R i j * (x i * x j) := by
      rw [Finset.sum_range_succ]
      have hlast : ∑ j ∈ range (s+1), padR (s := s) d.R s j * (x s * x j) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [padR_self, zero_mul]
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := mem_range.1 hi
      rw [Finset.sum_range_succ, padR_hi hi', zero_mul, add_zero]
      exact Finset.sum_congr rfl fun j hj => by rw [padR_lt hi' (mem_range.1 hj)]
    rw [h]; exact d.hRpsd x
  hRe := by
    intro i hi
    by_cases h : i < s
    · rw [padb_lt h, Finset.sum_range_succ, padR_hi h, add_zero, d.hRe i (mem_range.2 h)]
      exact Finset.sum_congr rfl fun j hj => (padR_lt h (mem_range.1 hj)).symm
    · have hs : i = s := by have := mem_range.1 hi; omega
      rw [hs, padb_self, Finset.sum_range_succ, padR_self, add_zero]
      exact (Finset.sum_eq_zero fun j _ => padR_self).symm
  h1 := by
    rw [Finset.sum_range_succ, padb_self, add_zero, ← d.h1]
    exact Finset.sum_congr rfl fun i hi => padb_lt (mem_range.1 hi)
  h2 := by
    rw [Finset.sum_range_succ, padb_self, zero_mul, add_zero, ← d.h2]
    exact Finset.sum_congr rfl fun i hi => by
      rw [padb_lt (mem_range.1 hi), padc_lt (mem_range.1 hi)]
  h3 := by
    rw [Finset.sum_range_succ, padb_self, zero_mul, add_zero, ← d.h3]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [padb_lt hi', Finset.sum_range_succ, padA_lt_hi hi', zero_mul, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by
      rw [padA_lt hi' (mem_range.1 hj), padc_lt (mem_range.1 hj)]
  h4 := by
    rw [Finset.sum_range_succ, padb_self, zero_mul, add_zero, ← d.h4]
    exact Finset.sum_congr rfl fun i hi => by
      rw [padb_lt (mem_range.1 hi), padc_lt (mem_range.1 hi)]
  hM := by
    intro i hi j hj
    have key : ∀ p q : ℕ, p < s → q < s →
        ∑ k ∈ range (s+1), padR (s := s) d.R p k * padA (s := s) d.A α k q
          = ∑ k ∈ range s, d.R p k * d.A k q := by
      intro p q hp hq
      rw [Finset.sum_range_succ, padR_hi hp, zero_mul, add_zero]
      exact Finset.sum_congr rfl fun k hk => by
        rw [padR_lt hp (mem_range.1 hk), padA_lt (mem_range.1 hk) hq]
    by_cases h1 : i < s
    · by_cases h2 : j < s
      · rw [key i j h1 h2, key j i h2 h1, padb_lt h1, padb_lt h2]
        exact d.hM i (mem_range.2 h1) j (mem_range.2 h2)
      · have hjs : j = s := by have := mem_range.1 hj; omega
        rw [hjs, padb_self, mul_zero, sub_zero]
        have e1 : ∑ k ∈ range (s+1), padR (s := s) d.R i k * padA (s := s) d.A α k s = 0 := by
          rw [Finset.sum_range_succ, padR_hi h1, zero_mul, add_zero]
          exact Finset.sum_eq_zero fun k hk => by
            rw [padA_lt_hi (mem_range.1 hk), mul_zero]
        have e2 : ∑ k ∈ range (s+1), padR (s := s) d.R s k * padA (s := s) d.A α k i = 0 :=
          Finset.sum_eq_zero fun k _ => by rw [padR_self, zero_mul]
        rw [e1, e2, add_zero]
    · have hs : i = s := by have := mem_range.1 hi; omega
      rw [hs, padb_self, zero_mul, sub_zero]
      have e1 : ∑ k ∈ range (s+1), padR (s := s) d.R s k * padA (s := s) d.A α k j = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [padR_self, zero_mul]
      rw [e1, zero_add]
      by_cases h2 : j < s
      · rw [Finset.sum_range_succ, padR_hi h2, zero_mul, add_zero]
        exact Finset.sum_eq_zero fun k hk => by rw [padA_lt_hi (mem_range.1 hk), mul_zero]
      · have hjs : j = s := by have := mem_range.1 hj; omega
        rw [hjs]
        exact Finset.sum_eq_zero fun k _ => by rw [padR_self, zero_mul]




/-- Every `AlgStabData` is a `WeakAlgStabData`: strict positivity of the weights is
stronger than the Claim's `b ≥ 0`.  So the six-stage witness of `algStabData_six_nonempty`
is in particular a witness in the weak sense. -/
def AlgStabData.toWeak {s : ℕ} (d : AlgStabData s) : WeakAlgStabData s where
  A := d.A
  b := d.b
  R := d.R
  c := d.c
  hA := d.hA
  hb := fun i hi => (d.hb i hi).le
  hc := d.hc
  hcmono := d.hcmono
  hcrange := d.hcrange
  hRsymm := d.hRsymm
  hRpsd := d.hRpsd
  hRe := d.hRe
  h1 := d.h1
  h2 := d.h2
  h3 := d.h3
  h4 := d.h4
  hM := d.hM

/-- The algebraic-stability matrix of a `WeakAlgStabData` is positive semidefinite — it is
zero.  This is the conclusion the Claim declares impossible. -/
theorem WeakAlgStabData.M_psd {s : ℕ} (d : WeakAlgStabData s) :
    PSDOn s (fun i j => (∑ k ∈ range s, d.R i k * d.A k j)
      + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) := by
  intro x
  have h : ∀ i ∈ range s, ∑ j ∈ range s,
      ((∑ k ∈ range s, d.R i k * d.A k j)
        + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) * (x i * x j) = 0 := by
    intro i hi
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [d.hM i hi j hj, zero_mul]
  rw [Finset.sum_congr rfl h]
  simp

/-! ### Iterating the padding

To iterate we must keep room above the abscissas, so we carry the strict bound `c < 1`
alongside the witness.  Padding with `α = (1 + M)/2`, where `M` is the current maximum
abscissa, preserves it. -/

/-- A witness together with the strict bound `c i < 1`, which is what leaves room for
another padded stage. -/
structure StrictWeak (s : ℕ) where
  /-- The underlying witness. -/
  data : WeakAlgStabData s
  /-- Every abscissa is strictly below `1`. -/
  hlt1 : ∀ i ∈ range s, data.c i < 1

/-- One padding step, staying inside `StrictWeak`.  The new abscissa is placed strictly
between the current maximum and `1`, so it is above every old abscissa and still `< 1`. -/
noncomputable def StrictWeak.step (w : StrictWeak s) {M : ℝ}
    (hM : ∀ i ∈ range s, w.data.c i ≤ M) (hM0 : 0 ≤ M) (hM1 : M < 1) :
    StrictWeak (s+1) where
  data := w.data.pad (α := (1 + M)/2)
    (fun i hi => lt_of_le_of_lt (hM i hi) (by linarith))
    (by linarith) (by linarith)
  hlt1 := by
    intro i hi
    change padc (s := s) w.data.c ((1+M)/2) i < 1
    by_cases h : i < s
    · rw [padc_lt h]; exact w.hlt1 i (mem_range.2 h)
    · have hs : i = s := by have := mem_range.1 hi; omega
      rw [hs, padc_self]; linarith




/-- On a finite stage range the abscissas attain a maximum `< 1`, so a padding step is
always available. -/
lemma StrictWeak.exists_step (w : StrictWeak s) : Nonempty (StrictWeak (s+1)) := by
  by_cases hs : s = 0
  · -- with no stages, `h1 : Σ b = 1` over an empty range reads `0 = 1`: impossible
    exfalso
    subst hs
    have h := w.data.h1
    simp at h
  · have hne : (range s).Nonempty := by
      refine Finset.nonempty_range_iff.2 ?_
      exact hs
    obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (range s) w.data.c hne
    refine ⟨w.step (M := w.data.c i0) hmax ?_ (w.hlt1 i0 hi0)⟩
    exact (w.data.hcrange i0 hi0).1

/-- **A `b ≥ 0` witness at `s` stages gives one at every larger stage count.** -/
theorem StrictWeak.exists_all (w : StrictWeak s) : ∀ n, Nonempty (StrictWeak (s + n)) := by
  intro n
  induction n with
  | zero => exact ⟨w⟩
  | succ m ih =>
      obtain ⟨wm⟩ := ih
      have := wm.exists_step
      exact ⟨this.some⟩



namespace Six

/-! ## The parameter `τ` -/

/-- The defining cubic of the construction parameter: `192 x³ + 96 x² − 1`. -/
noncomputable def cub (x : ℝ) : ℝ := 192 * x ^ 3 + 96 * x ^ 2 - 1

lemma cub_continuous : Continuous cub := by
  unfold cub; fun_prop

lemma cub_lower : cub (9366 / 100000) < 0 := by
  unfold cub; norm_num

lemma cub_upper : 0 < cub (9367 / 100000) := by
  unfold cub; norm_num

/-- **The construction parameter exists**, inside an explicit rational bracket of width
`10⁻⁵`.  Every sign assertion below is decided from this bracket alone. -/
theorem tau_exists :
    ∃ τ : ℝ, τ ∈ Set.Ioo (9366 / 100000 : ℝ) (9367 / 100000) ∧ cub τ = 0 := by
  obtain ⟨τ, hτ, h0⟩ :=
    intermediate_value_Ioo (by norm_num : (9366 / 100000 : ℝ) ≤ 9367 / 100000)
      cub_continuous.continuousOn (Set.mem_Ioo.2 ⟨cub_lower, cub_upper⟩)
  exact ⟨τ, hτ, h0⟩

/-! ## The explicit data of the construction

`Xm` is the symmetric rank-3 matrix `X`, `hv` the vector `h`, `Gm` the circulant
`G = (1/4)P + t P²`, and `vv s` the point of the rational line at parameter `s`.
All are explicit polynomials in `t` of degree ≤ 2. -/

/-- The circulant `G = (1/4) P + t P²` on `range 6`. -/
noncomputable def Gm (t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 1 => ((1/4 : ℝ))
  | 0, 2 => ((0 : ℝ) + (1 : ℝ) * t)
  | 1, 2 => ((1/4 : ℝ))
  | 1, 3 => ((0 : ℝ) + (1 : ℝ) * t)
  | 2, 3 => ((1/4 : ℝ))
  | 2, 4 => ((0 : ℝ) + (1 : ℝ) * t)
  | 3, 4 => ((1/4 : ℝ))
  | 3, 5 => ((0 : ℝ) + (1 : ℝ) * t)
  | 4, 0 => ((0 : ℝ) + (1 : ℝ) * t)
  | 4, 5 => ((1/4 : ℝ))
  | 5, 0 => ((1/4 : ℝ))
  | 5, 1 => ((0 : ℝ) + (1 : ℝ) * t)
  | _, _ => 0

/-- The vector `h`, with `X v = h`. -/
noncomputable def hv (t : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2)
  | 1 => ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2)
  | 2 => ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2)
  | 3 => ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2)
  | 4 => ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2)
  | 5 => ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2)
  | _ => 0

/-- The symmetric rank-3 matrix `X = B S Bᵗ`. -/
noncomputable def Xm (t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2)
  | 0, 1 => ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2)
  | 0, 2 => ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2)
  | 0, 3 => ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2)
  | 0, 4 => ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2)
  | 0, 5 => ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2)
  | 1, 0 => ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2)
  | 1, 1 => ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2)
  | 1, 2 => ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2)
  | 1, 3 => ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2)
  | 1, 4 => ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2)
  | 1, 5 => ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2)
  | 2, 0 => ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2)
  | 2, 1 => ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2)
  | 2, 2 => ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2)
  | 2, 3 => ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2)
  | 2, 4 => ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2)
  | 2, 5 => ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2)
  | 3, 0 => ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2)
  | 3, 1 => ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2)
  | 3, 2 => ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2)
  | 3, 3 => ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2)
  | 3, 4 => ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2)
  | 3, 5 => ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2)
  | 4, 0 => ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2)
  | 4, 1 => ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2)
  | 4, 2 => ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2)
  | 4, 3 => ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2)
  | 4, 4 => ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2)
  | 4, 5 => ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2)
  | 5, 0 => ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2)
  | 5, 1 => ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2)
  | 5, 2 => ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2)
  | 5, 3 => ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2)
  | 5, 4 => ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2)
  | 5, 5 => ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2)
  | _, _ => 0

/-- The rational line `v(s) = (21/8 − s, 17/4 + 2s, 17/4 − 2s, 7/4 + s, 1, 3/2)`. -/
noncomputable def vv (s : ℝ) : ℕ → ℝ := fun i =>
  match i with
  | 0 => 21/8 - s
  | 1 => 17/4 + 2*s
  | 2 => 17/4 - 2*s
  | 3 => 7/4 + s
  | 4 => 1
  | 5 => 3/2
  | _ => 0

/-- `Xm` is symmetric. -/
lemma Xm_symm (t : ℝ) : ∀ i ∈ Finset.range 6, ∀ j ∈ Finset.range 6,
    Xm t i j = Xm t j i := by
  intro i hi j hj
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp [Xm]

/-! ## `X G + Gᵗ X = h hᵗ`: the 21 entries

Each raw polynomial in `t` is exactly divisible by `192t³ + 96t² − 1`; the quotient is
supplied to `linear_combination` as the certificate. -/

lemma XGid_0_0 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2) + ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) + ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) + ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) + ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ) + (1 : ℝ) * t) * ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) + ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((1/4 : ℝ)) * ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2)
      = ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2) * ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-250383872/1833680187 : ℝ) + (-755590144/1833680187 : ℝ) * t) * ht

lemma XGid_0_1 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) + ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2) + ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) + ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) + ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) + ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((1/4 : ℝ)) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2)
      = ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2) * ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-179613280/1833680187 : ℝ) + (-70369280/1833680187 : ℝ) * t) * ht

lemma XGid_0_2 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) + ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) + ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2) + ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) + ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2)
      = ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2) * ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2) := by
  linear_combination ((18645664/1833680187 : ℝ) + (596819456/1833680187 : ℝ) * t) * ht

lemma XGid_0_3 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) + ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) + ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) + ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2) + ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2)
      = ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2) * ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2) := by
  linear_combination ((146134016/1833680187 : ℝ) + (578787328/1833680187 : ℝ) * t) * ht

lemma XGid_0_4 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) + ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) + ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2) + ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2)
      = ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2) * ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2) := by
  linear_combination ((75363424/1833680187 : ℝ) + (-106433536/1833680187 : ℝ) * t) * ht

lemma XGid_0_5 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((1222315712/1833680187 : ℝ) + (-369410048/67914081 : ℝ) * t + (-966123520/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) + ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) + ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) + ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) + ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) + ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2)
      = ((12520/24723 : ℝ) + (-75968/24723 : ℝ) * t + (-219904/24723 : ℝ) * t ^ 2) * ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-122895520/1833680187 : ℝ) + (-773622272/1833680187 : ℝ) * t) * ht

lemma XGid_1_1 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((1/4 : ℝ)) * ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) + ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) + ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) + ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ) + (1 : ℝ) * t) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2)
      = ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2) * ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2) := by
  linear_combination ((5196352/1833680187 : ℝ) + (-6553600/1833680187 : ℝ) * t) * ht

lemma XGid_1_2 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((1/4 : ℝ)) * ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) + ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) + ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2)
      = ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2) * ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2) := by
  linear_combination ((147188864/1833680187 : ℝ) + (55582720/1833680187 : ℝ) * t) * ht

lemma XGid_1_3 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) + ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2) + ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2)
      = ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2) * ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2) := by
  linear_combination ((104371744/1833680187 : ℝ) + (53903360/1833680187 : ℝ) * t) * ht

lemma XGid_1_4 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) + ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2) + ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2)
      = ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2) * ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-80437888/1833680187 : ℝ) + (-9912320/1833680187 : ℝ) * t) * ht

lemma XGid_1_5 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((43895680/1833680187 : ℝ) + (-7434496/67914081 : ℝ) * t + (-75618304/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) + ((80206592/1833680187 : ℝ) + (-18129920/67914081 : ℝ) * t + (-132674560/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) + ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) + ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2)
      = ((3008/24723 : ℝ) + (-11680/24723 : ℝ) * t + (-20480/24723 : ℝ) * t ^ 2) * ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-222430400/1833680187 : ℝ) + (-72048640/1833680187 : ℝ) * t) * ht

lemma XGid_2_2 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ) + (1 : ℝ) * t) * ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((1/4 : ℝ)) * ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) + ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2) + ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) + ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2)
      = ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2) * ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2) := by
  linear_combination ((129688096/1833680187 : ℝ) + (-471410944/1833680187 : ℝ) * t) * ht

lemma XGid_2_3 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((1/4 : ℝ)) * ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) + ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) + ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2) + ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2)
      = ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2) * ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-16355872/1833680187 : ℝ) + (-457167872/1833680187 : ℝ) * t) * ht

lemma XGid_2_4 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) + ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2) + ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2)
      = ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2) * ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-144899072/1833680187 : ℝ) + (84068864/1833680187 : ℝ) * t) * ht

lemma XGid_2_5 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((-915569920/1833680187 : ℝ) + (2572403200/611226729 : ℝ) * t + (739644416/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) + ((20681152/1833680187 : ℝ) + (-46054912/611226729 : ℝ) * t + (-13901824/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) + ((727584128/1833680187 : ℝ) + (-2038017280/611226729 : ℝ) * t + (-1728360448/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) + ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) + ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) + ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2)
      = ((-6832/24723 : ℝ) + (57856/24723 : ℝ) * t + (173696/24723 : ℝ) * t ^ 2) * ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-127398304/1833680187 : ℝ) + (611062528/1833680187 : ℝ) * t) * ht

lemma XGid_3_3 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ) + (1 : ℝ) * t) * ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) + ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((1/4 : ℝ)) * ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) + ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2) + ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2)
      = ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2) * ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-95321216/1833680187 : ℝ) + (-443355136/1833680187 : ℝ) * t) * ht

lemma XGid_3_4 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) + ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((1/4 : ℝ)) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2) + ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2)
      = ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2) * ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2) := by
  linear_combination ((-53558944/1833680187 : ℝ) + (81528832/1833680187 : ℝ) * t) * ht

lemma XGid_3_5 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((-696615488/1833680187 : ℝ) + (1953936896/611226729 : ℝ) * t + (1690732544/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) + ((-75155200/1833680187 : ℝ) + (167318272/611226729 : ℝ) * t + (161927168/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) + ((498236032/1833680187 : ℝ) + (-1411521536/611226729 : ℝ) * t + (-403328000/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((1/4 : ℝ)) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) + ((450166976/1833680187 : ℝ) + (-1203742720/611226729 : ℝ) * t + (-1053089792/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) + ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) + ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2)
      = ((-7160/24723 : ℝ) + (63104/24723 : ℝ) * t + (168448/24723 : ℝ) * t ^ 2) * ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2) := by
  linear_combination ((67168672/1833680187 : ℝ) + (592600064/1833680187 : ℝ) * t) * ht

lemma XGid_4_4 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) + ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) + ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ) + (1 : ℝ) * t) * ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) + ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((1/4 : ℝ)) * ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) + ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2) + ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2)
      = ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2) * ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2) := by
  linear_combination ((102242368/1833680187 : ℝ) + (-14992384/1833680187 : ℝ) * t) * ht

lemma XGid_4_5 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((481804544/1833680187 : ℝ) + (-1303843072/611226729 : ℝ) * t + (-41926656/7546009 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) + ((-111466112/1833680187 : ℝ) + (263577088/611226729 : ℝ) * t + (218983424/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) + ((-438015040/1833680187 : ℝ) + (134104064/67914081 : ℝ) * t + (1022851072/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ) + (1 : ℝ) * t) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) + ((-171293312/1833680187 : ℝ) + (194291968/203742243 : ℝ) * t + (475715584/203742243 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((1/4 : ℝ)) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) + ((421977344/1833680187 : ℝ) + (-984544256/611226729 : ℝ) * t + (-875287552/203742243 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((0 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) + ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2)
      = ((784/8241 : ℝ) + (-1184/24723 : ℝ) * t + (-30976/24723 : ℝ) * t ^ 2) * ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2) := by
  linear_combination ((166703552/1833680187 : ℝ) + (-108973568/1833680187 : ℝ) * t) * ht

lemma XGid_5_5 (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1441270144/1833680187 : ℝ) + (-3943156736/611226729 : ℝ) * t + (-3426571264/203742243 : ℝ) * t ^ 2) + ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-51940672/1833680187 : ℝ) + (146462720/611226729 : ℝ) * t + (100210688/203742243 : ℝ) * t ^ 2) + ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((-1144918016/1833680187 : ℝ) + (355433216/67914081 : ℝ) * t + (2737309696/203742243 : ℝ) * t ^ 2) + ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) * ((0 : ℝ) + (1 : ℝ) * t) + ((0 : ℝ) + (1 : ℝ) * t) * ((-744684544/1833680187 : ℝ) + (720571904/203742243 : ℝ) * t + (615875584/67914081 : ℝ) * t ^ 2) + ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) * ((1/4 : ℝ)) + ((1/4 : ℝ)) * ((748526272/1833680187 : ℝ) + (-1927903744/611226729 : ℝ) * t + (-186572800/22638027 : ℝ) * t ^ 2) + ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2) * ((0 : ℝ)) + ((0 : ℝ)) * ((1841503616/1833680187 : ℝ) + (-4980339968/611226729 : ℝ) * t + (-4316254208/203742243 : ℝ) * t ^ 2)
      = ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2) * ((4064/8241 : ℝ) + (-70720/24723 : ℝ) * t + (-225152/24723 : ℝ) * t ^ 2) := by
  linear_combination ((71671456/1833680187 : ℝ) + (-792084736/1833680187 : ℝ) * t) * ht

set_option maxHeartbeats 4000000 in
/-- **The defining identity of `X`**, in matrix form on `range 6`.
Dispatches to the 21 entry lemmas above (using symmetry of the statement in `i`,`j`). -/
lemma XG_add_GtX (t : ℝ) (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0) :
    ∀ i ∈ Finset.range 6, ∀ j ∈ Finset.range 6,
      (∑ k ∈ Finset.range 6, Xm t i k * Gm t k j)
        + (∑ k ∈ Finset.range 6, Gm t k i * Xm t k j) = hv t i * hv t j := by
  intro i hi j hj
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  simp only [show (6:ℕ) = 5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> interval_cases j <;> simp only [Xm, Gm, hv]
  case _ => linear_combination XGid_0_0 t ht
  case _ => linear_combination XGid_0_1 t ht
  case _ => linear_combination XGid_0_2 t ht
  case _ => linear_combination XGid_0_3 t ht
  case _ => linear_combination XGid_0_4 t ht
  case _ => linear_combination XGid_0_5 t ht
  case _ => linear_combination XGid_0_1 t ht
  case _ => linear_combination XGid_1_1 t ht
  case _ => linear_combination XGid_1_2 t ht
  case _ => linear_combination XGid_1_3 t ht
  case _ => linear_combination XGid_1_4 t ht
  case _ => linear_combination XGid_1_5 t ht
  case _ => linear_combination XGid_0_2 t ht
  case _ => linear_combination XGid_1_2 t ht
  case _ => linear_combination XGid_2_2 t ht
  case _ => linear_combination XGid_2_3 t ht
  case _ => linear_combination XGid_2_4 t ht
  case _ => linear_combination XGid_2_5 t ht
  case _ => linear_combination XGid_0_3 t ht
  case _ => linear_combination XGid_1_3 t ht
  case _ => linear_combination XGid_2_3 t ht
  case _ => linear_combination XGid_3_3 t ht
  case _ => linear_combination XGid_3_4 t ht
  case _ => linear_combination XGid_3_5 t ht
  case _ => linear_combination XGid_0_4 t ht
  case _ => linear_combination XGid_1_4 t ht
  case _ => linear_combination XGid_2_4 t ht
  case _ => linear_combination XGid_3_4 t ht
  case _ => linear_combination XGid_4_4 t ht
  case _ => linear_combination XGid_4_5 t ht
  case _ => linear_combination XGid_0_5 t ht
  case _ => linear_combination XGid_1_5 t ht
  case _ => linear_combination XGid_2_5 t ht
  case _ => linear_combination XGid_3_5 t ht
  case _ => linear_combination XGid_4_5 t ht
  case _ => linear_combination XGid_5_5 t ht

/-! ## `X v = h` along the line -/

/-- `X v(s) = h` for **every** `s`: the direction `(−1,2,−2,1,0,0)` lies in the kernel
of `Bᵗ`, so `z = Bᵗ v(s)` — and hence `h`, `S`, `X` — do not depend on `s`. -/
lemma Xv_eq_h (t s : ℝ) : ∀ i ∈ Finset.range 6,
    (∑ k ∈ Finset.range 6, Xm t i k * vv s k) = hv t i := by
  intro i hi
  have hi' := Finset.mem_range.1 hi
  simp only [show (6:ℕ) = 5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  interval_cases i <;> simp only [Xm, vv, hv] <;> ring

/-! ## The transported tableau

With `D = diag v(σ)` we set `A = D⁻¹ G D`, `b = D h`, `R = D X D`, `c = A e`.  Everything
in this section holds for every `σ` in the parameter interval and every `t` in the
`τ`-bracket; only the order-three condition (next section) singles out a `σ`. -/

/-- `A = D⁻¹ G D`, entrywise `A i j = G i j · v j / v i`. -/
noncomputable def Am (t s : ℝ) : ℕ → ℕ → ℝ := fun i j => Gm t i j * vv s j / vv s i

/-- `b = D h`. -/
noncomputable def bvec (t s : ℝ) : ℕ → ℝ := fun i => vv s i * hv t i

/-- `R = D X D`. -/
noncomputable def Rm (t s : ℝ) : ℕ → ℕ → ℝ := fun i j => vv s i * Xm t i j * vv s j

/-- `c = A e`, written as `(G v) i / v i`. -/
noncomputable def cvec (t s : ℝ) : ℕ → ℝ := fun i =>
  (∑ j ∈ range 6, Gm t i j * vv s j) / vv s i

/-- Every coordinate of `v(σ)` is positive on the parameter interval. -/
lemma vv_pos {s : ℝ} (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) : ∀ i ∈ range 6, 0 < vv s i := by
  obtain ⟨h1, h2⟩ := hs
  intro i hi
  have hi' := mem_range.1 hi
  interval_cases i <;> simp only [vv] <;> linarith

/-- **`A ≥ 0` entrywise**: immediate from `G ≥ 0` and `v > 0`. -/
lemma Am_nonneg {t s : ℝ} (ht : 0 < t) (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∀ i ∈ range 6, ∀ j ∈ range 6, 0 ≤ Am t s i j := by
  intro i hi j hj
  have hvi := vv_pos hs i hi
  have hvj := vv_pos hs j hj
  have hg : 0 ≤ Gm t i j := by
    have hi' := mem_range.1 hi
    have hj' := mem_range.1 hj
    interval_cases i <;> interval_cases j <;> simp only [Gm] <;> linarith
  unfold Am
  positivity

/-- **`b > 0`** on the stage range, for `t` in the bracket. -/
lemma bvec_pos {t s : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000))
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) : ∀ i ∈ range 6, 0 < bvec t s i := by
  obtain ⟨ht1, ht2⟩ := ht
  intro i hi
  have hvi := vv_pos hs i hi
  have hh : 0 < hv t i := by
    have hi' := mem_range.1 hi
    interval_cases i <;> simp only [hv] <;> nlinarith
  unfold bvec
  positivity

/-- **`c = A e`**: the abscissas are the row sums of `A`. -/
lemma cvec_eq_rowsum (t s : ℝ) : ∀ i ∈ range 6, cvec t s i = ∑ j ∈ range 6, Am t s i j := by
  intro i _
  unfold cvec Am
  rw [← Finset.sum_div]

/-- **`R e = b`**, transported from `X v = h`. -/
lemma Rm_rowsum (t s : ℝ) : ∀ i ∈ range 6, ∑ j ∈ range 6, Rm t s i j = bvec t s i := by
  intro i hi
  unfold Rm bvec
  have h : ∑ j ∈ range 6, vv s i * Xm t i j * vv s j
      = vv s i * ∑ j ∈ range 6, Xm t i j * vv s j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, Xv_eq_h t s i hi]

/-- `R` is symmetric. -/
lemma Rm_symm (t s : ℝ) : ∀ i ∈ range 6, ∀ j ∈ range 6, Rm t s i j = Rm t s j i := by
  intro i hi j hj
  unfold Rm
  rw [Xm_symm t i hi j hj]; ring

/-- **`M = R A + Aᵗ R − b bᵗ = 0`**, transported from `X G + Gᵗ X = h hᵗ` by conjugation
with `D`.  Each sum factors as `v i · (…) · v j`, and the `X`-identity then closes it. -/
lemma Mm_zero {t s : ℝ} (ht : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0)
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∀ i ∈ range 6, ∀ j ∈ range 6,
      (∑ k ∈ range 6, Rm t s i k * Am t s k j)
        + (∑ k ∈ range 6, Rm t s j k * Am t s k i)
        - bvec t s i * bvec t s j = 0 := by
  intro i hi j hj
  have key : ∀ (p q : ℕ), q ∈ range 6 →
      ∑ k ∈ range 6, Rm t s p k * Am t s k q
        = vv s p * (∑ k ∈ range 6, Xm t p k * Gm t k q) * vv s q := by
    intro p q _
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hvk := (vv_pos hs k hk).ne'
    unfold Rm Am
    field_simp
  rw [key i j hj, key j i hi]
  have h1 := XG_add_GtX t ht i hi j hj
  have hsym : ∑ k ∈ range 6, Xm t j k * Gm t k i = ∑ k ∈ range 6, Gm t k i * Xm t k j := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Xm_symm t j hj k hk, mul_comm]
  rw [hsym]
  unfold bvec
  linear_combination (vv s i * vv s j) * h1

/-! ### Positive semidefiniteness of `R`

`X = B S Bᵗ` with `S` the `3 × 3` reduced matrix, so `xᵗXx = (Bᵗx)ᵗ S (Bᵗx)`, and
`xᵗRx = (Dx)ᵗ X (Dx)`.  It therefore suffices that `S` be positive semidefinite, which
we get from Sylvester's criterion made explicit as a completion of squares. -/

/-- The `3 × 3` reduced matrix `S`, with `X = B S Bᵗ`. -/
noncomputable def Sm (t : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  match i, j with
  | 0, 0 => (64/1681 : ℝ) + (-1280/5043 : ℝ)*t + (-31744/45387 : ℝ)*t^2
  | 0, 1 | 1, 0 => (3904/74169 : ℝ) + (-96512/222507 : ℝ)*t + (-2048/1809 : ℝ)*t^2
  | 0, 2 | 2, 0 => (-7360/74169 : ℝ) + (57088/74169 : ℝ)*t + (151552/74169 : ℝ)*t^2
  | 1, 1 => (113984/1090827 : ℝ) + (-313664/363609 : ℝ)*t + (-90880/40401 : ℝ)*t^2
  | 1, 2 | 2, 1 => (-51232/363609 : ℝ) + (436544/363609 : ℝ)*t + (374528/121203 : ℝ)*t^2
  | 2, 2 => (33472/121203 : ℝ) + (-269504/121203 : ℝ)*t + (-691456/121203 : ℝ)*t^2
  | _, _ => 0

/-- First leading principal minor of `S`. -/
noncomputable def sm1 (t : ℝ) : ℝ := Sm t 0 0

/-- Second leading principal minor of `S`. -/
noncomputable def sm2 (t : ℝ) : ℝ := Sm t 0 0 * Sm t 1 1 - Sm t 0 1 * Sm t 0 1

/-- Third leading principal minor of `S`, i.e. `det S`. -/
noncomputable def sm3 (t : ℝ) : ℝ :=
  Sm t 0 0 * (Sm t 1 1 * Sm t 2 2 - Sm t 1 2 * Sm t 1 2)
    - Sm t 0 1 * (Sm t 0 1 * Sm t 2 2 - Sm t 1 2 * Sm t 0 2)
    + Sm t 0 2 * (Sm t 0 1 * Sm t 1 2 - Sm t 1 1 * Sm t 0 2)

lemma sm1_pos {t : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000)) : 0 < sm1 t := by
  obtain ⟨h1, h2⟩ := ht
  simp only [sm1, Sm]
  nlinarith [sq_nonneg t, sq_nonneg (t - 9366/100000)]

lemma sm2_pos {t : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000)) : 0 < sm2 t := by
  obtain ⟨h1, h2⟩ := ht
  simp only [sm2, Sm]
  nlinarith [sq_nonneg t, sq_nonneg (t - 9366/100000), sq_nonneg (t*t), sq_nonneg (t*t*t)]

lemma sm3_pos {t : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000)) : 0 < sm3 t := by
  obtain ⟨h1, h2⟩ := ht
  simp only [sm3, Sm]
  nlinarith [sq_nonneg t, sq_nonneg (t - 9366/100000), sq_nonneg (t*t), sq_nonneg (t*t*t),
    sq_nonneg (t*t*t*t)]

/-- **The quadratic form of `S` is nonnegative** on the bracket.  Completion of squares:
with `B = S₀₀S₁₂ − S₀₁S₀₂`,
`m₁·m₂·Q = m₂·(S₀₀x₀+S₀₁x₁+S₀₂x₂)² + (m₂x₁+Bx₂)² + m₁·m₃·x₂²`. -/
lemma Sm_psd {t : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000)) (x0 x1 x2 : ℝ) :
    0 ≤ Sm t 0 0 * x0^2 + 2*Sm t 0 1 * x0*x1 + 2*Sm t 0 2 * x0*x2
      + Sm t 1 1 * x1^2 + 2*Sm t 1 2 * x1*x2 + Sm t 2 2 * x2^2 := by
  have h1 := sm1_pos ht
  have h2 := sm2_pos ht
  have h3 := sm3_pos ht
  set Q : ℝ := Sm t 0 0 * x0^2 + 2*Sm t 0 1 * x0*x1 + 2*Sm t 0 2 * x0*x2
      + Sm t 1 1 * x1^2 + 2*Sm t 1 2 * x1*x2 + Sm t 2 2 * x2^2 with hQ
  set B : ℝ := Sm t 0 0 * Sm t 1 2 - Sm t 0 1 * Sm t 0 2 with hB
  have key : sm1 t * sm2 t * Q
      = sm2 t * (Sm t 0 0 * x0 + Sm t 0 1 * x1 + Sm t 0 2 * x2)^2
        + (sm2 t * x1 + B * x2)^2 + sm1 t * sm3 t * x2^2 := by
    simp only [hQ, hB, sm1, sm2, sm3]; ring
  have hrhs : 0 ≤ sm2 t * (Sm t 0 0 * x0 + Sm t 0 1 * x1 + Sm t 0 2 * x2)^2
        + (sm2 t * x1 + B * x2)^2 + sm1 t * sm3 t * x2^2 := by positivity
  nlinarith [key, hrhs, mul_pos h1 h2]

/-- **`X = B S Bᵗ` at the level of quadratic forms**: `xᵗXx = uᵗSu` with `u = Bᵗx`, i.e.
`u₀ = Σxᵢ`, `u₁ = 2x₀+x₁−x₂−2x₃−x₄+x₅`, `u₂ = x₁+x₂−x₄−x₅`. -/
lemma Xm_quadform (t : ℝ) (x : ℕ → ℝ) :
    ∑ i ∈ range 6, ∑ j ∈ range 6, Xm t i j * (x i * x j)
      = Sm t 0 0 * (x 0 + x 1 + x 2 + x 3 + x 4 + x 5)^2
        + 2*Sm t 0 1 * (x 0 + x 1 + x 2 + x 3 + x 4 + x 5)
            * (2*x 0 + x 1 - x 2 - 2*x 3 - x 4 + x 5)
        + 2*Sm t 0 2 * (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) * (x 1 + x 2 - x 4 - x 5)
        + Sm t 1 1 * (2*x 0 + x 1 - x 2 - 2*x 3 - x 4 + x 5)^2
        + 2*Sm t 1 2 * (2*x 0 + x 1 - x 2 - 2*x 3 - x 4 + x 5) * (x 1 + x 2 - x 4 - x 5)
        + Sm t 2 2 * (x 1 + x 2 - x 4 - x 5)^2 := by
  simp only [show (6:ℕ) = 5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, Xm, Sm]
  ring

/-- **`X` is positive semidefinite** on the bracket. -/
lemma Xm_psd {t : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000)) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range 6, ∑ j ∈ range 6, Xm t i j * (x i * x j) := by
  rw [Xm_quadform]
  exact Sm_psd ht _ _ _

/-- **`R = D X D` is positive semidefinite**: its form at `x` is `X`'s at `Dx`. -/
lemma Rm_psd {t : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000)) (s : ℝ)
    (x : ℕ → ℝ) : 0 ≤ ∑ i ∈ range 6, ∑ j ∈ range 6, Rm t s i j * (x i * x j) := by
  have h : ∑ i ∈ range 6, ∑ j ∈ range 6, Rm t s i j * (x i * x j)
      = ∑ i ∈ range 6, ∑ j ∈ range 6, Xm t i j * ((vv s i * x i) * (vv s j * x j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold Rm; ring
  rw [h]
  exact Xm_psd ht (fun i => vv s i * x i)

/-! ### The abscissas -/

/-- **The abscissas lie strictly inside `(0,1)`** on the parameter rectangle. -/
lemma cvec_mem {t s : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000))
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∀ i ∈ range 6, 0 < cvec t s i ∧ cvec t s i < 1 := by
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hs1, hs2⟩ := hs
  intro i hi
  have hi' := mem_range.1 hi
  have hv := vv_pos ⟨hs1, hs2⟩ i hi
  unfold cvec
  simp only [show (6:ℕ) = 5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  have ht0 : (0:ℝ) < t := by linarith
  interval_cases i <;> simp only [Gm, vv] at hv ⊢ <;>
    refine ⟨div_pos (by nlinarith) (by linarith), ?_⟩ <;>
      rw [div_lt_one (by linarith)] <;> nlinarith

/-- **The abscissas are strictly ordered** along the fixed permutation `(3,1,2,4,5,0)`:
`c₃ < c₁ < c₂ < c₄ < c₅ < c₀`, uniformly on the parameter rectangle.  In particular they
are pairwise distinct, and a single relabelling sorts the tableau for every `σ`. -/
lemma cvec_sorted {t s : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000))
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    cvec t s 3 < cvec t s 1 ∧ cvec t s 1 < cvec t s 2 ∧ cvec t s 2 < cvec t s 4
      ∧ cvec t s 4 < cvec t s 5 ∧ cvec t s 5 < cvec t s 0 := by
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hs1, hs2⟩ := hs
  have ht0 : (0:ℝ) < t := by linarith
  have h0 : (0:ℝ) < 21/8 - s := by linarith
  have h1 : (0:ℝ) < 17/4 + 2*s := by linarith
  have h2 : (0:ℝ) < 17/4 - 2*s := by linarith
  have h3 : (0:ℝ) < 7/4 + s := by linarith
  unfold cvec
  simp only [show (6:ℕ) = 5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, Gm, vv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [div_lt_div_iff₀ (by linarith) (by linarith)] <;>
    nlinarith [mul_pos h0 h1, mul_pos h1 h2, mul_pos h2 h3, mul_pos h0 h3,
      mul_pos ht0 h0, mul_pos ht0 h1, mul_pos ht0 h2, mul_pos ht0 h3,
      sq_nonneg s, sq_nonneg (s - 1/2), sq_nonneg (3/4 - s),
      mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hs2)]

/-! ### Everything except the order-three condition, packaged -/

/-- **Ten of the eleven conditions of the Claim, uniformly in the parameter.**
For every `t` satisfying the cubic and lying in the bracket, and every `σ` in
`[1/2, 3/4]`, the transported tableau `(A, b, R, c)` satisfies: `A ≥ 0`, `b > 0`,
`c = A e` with entries in `(0,1)` strictly ordered by the fixed permutation
`(3,1,2,4,5,0)`, `R` symmetric positive semidefinite with `R e = b`, and `M = 0`.

The only condition *not* listed is `bᵀc² = 1/3`; that is what the next section pins. -/
theorem uniform_conditions {t s : ℝ}
    (htc : 192 * t ^ 3 + 96 * t ^ 2 - 1 = 0)
    (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000))
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    (∀ i ∈ range 6, ∀ j ∈ range 6, 0 ≤ Am t s i j)
      ∧ (∀ i ∈ range 6, 0 < bvec t s i)
      ∧ (∀ i ∈ range 6, cvec t s i = ∑ j ∈ range 6, Am t s i j)
      ∧ (∀ i ∈ range 6, 0 < cvec t s i ∧ cvec t s i < 1)
      ∧ (cvec t s 3 < cvec t s 1 ∧ cvec t s 1 < cvec t s 2 ∧ cvec t s 2 < cvec t s 4
          ∧ cvec t s 4 < cvec t s 5 ∧ cvec t s 5 < cvec t s 0)
      ∧ (∀ i ∈ range 6, ∀ j ∈ range 6, Rm t s i j = Rm t s j i)
      ∧ (∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 6, ∑ j ∈ range 6, Rm t s i j * (x i * x j))
      ∧ (∀ i ∈ range 6, ∑ j ∈ range 6, Rm t s i j = bvec t s i)
      ∧ (∀ i ∈ range 6, ∀ j ∈ range 6,
          (∑ k ∈ range 6, Rm t s i k * Am t s k j)
            + (∑ k ∈ range 6, Rm t s j k * Am t s k i)
            - bvec t s i * bvec t s j = 0) := by
  have ht0 : (0:ℝ) < t := by have := ht.1; linarith
  exact ⟨Am_nonneg ht0 hs, bvec_pos ht hs, cvec_eq_rowsum t s, cvec_mem ht hs,
    cvec_sorted ht hs, Rm_symm t s, Rm_psd ht s, Rm_rowsum t s, Mm_zero htc hs⟩

/-! ### The sorting relabelling

`cvec_sorted` gives the order `c₃ < c₁ < c₂ < c₄ < c₅ < c₀`, the *same* for every parameter
value.  So a single fixed permutation sorts the tableau, and `AlgStabData`'s requirement
that `c` be increasing in the index is met after relabelling by it. -/

/-- The relabelling that sorts the abscissas: `perm k` is the original stage index that
becomes stage `k`.  Indices `≥ 6` are sent to `6`, where `v` vanishes. -/
def perm : ℕ → ℕ := fun k =>
  match k with
  | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 0 | _ => 6

lemma perm_mem : ∀ k ∈ range 6, perm k ∈ range 6 := by
  intro k hk
  have := mem_range.1 hk
  interval_cases k <;> simp [perm]

/-- Outside the stage range the relabelling sends the index to `6`, where `v` vanishes. -/
lemma perm_eq_six {k : ℕ} (hk : ¬ k < 6) : perm k = 6 := by
  match k, hk with
  | 0, h => omega
  | 1, h => omega
  | 2, h => omega
  | 3, h => omega
  | 4, h => omega
  | 5, h => omega
  | (n+6), _ => rfl

/-- `perm` permutes `range 6`, so reindexing a sum by it is harmless. -/
lemma sum_perm (f : ℕ → ℝ) : ∑ k ∈ range 6, f (perm k) = ∑ i ∈ range 6, f i := by
  simp only [show (6:ℕ) = 5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, perm]
  ring

/-- **`A ≥ 0` globally** (as `AlgStabData.hA` demands): off `range 6` the coefficient
vanishes, because `vv` does and division by zero is zero. -/
lemma Am_nonneg_all {t s : ℝ} (ht : 0 < t) (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∀ i j, 0 ≤ Am t s (perm i) (perm j) := by
  intro i j
  by_cases hi : i < 6
  · by_cases hj : j < 6
    · exact Am_nonneg ht hs _ (perm_mem i (mem_range.2 hi)) _ (perm_mem j (mem_range.2 hj))
    · simp [Am, perm_eq_six hj, vv]
  · simp [Am, perm_eq_six hi, vv]

/-- **The permuted abscissas are strictly increasing in the index.** -/
lemma cvec_perm_mono {t s : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000))
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∀ i ∈ range 6, ∀ j ∈ range 6, i < j → cvec t s (perm i) < cvec t s (perm j) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := cvec_sorted ht hs
  intro i hi j hj hij
  have hi' := mem_range.1 hi
  have hj' := mem_range.1 hj
  interval_cases i <;> interval_cases j <;> simp only [perm] <;>
    first
      | exact absurd hij (by omega)
      | linarith

/-! ### The order conditions, and the defect, evaluated on the tableau

At each endpoint the four moment sums are finite sums of explicit rationals in `t`, so each
reduces (after clearing the `v`-denominators, which are concrete nonzero rationals) to a
polynomial identity in `t` modulo the cubic.  As with the `X`-identities the residual is
exactly divisible by `192t³+96t²−1`, and the quotient is the `linear_combination`
certificate. -/

/-- `bᵀe = 1` at `σ = 1/2` (no cubic needed). -/
lemma m0_L (t : ℝ) : ∑ i ∈ range 6, bvec t (1/2) i = 1 := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bvec, hv, vv]
  ring_nf

/-- `bᵀe = 1` at `σ = 3/4`. -/
lemma m0_R (t : ℝ) : ∑ i ∈ range 6, bvec t (3/4) i = 1 := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bvec, hv, vv]
  ring_nf

/-- `bᵀc = 1/2` at `σ = 1/2`. -/
lemma m1_L (t : ℝ) (ht : 192*t^3 + 96*t^2 - 1 = 0) :
    ∑ i ∈ range 6, bvec t (1/2) i * cvec t (1/2) i = 1/2 := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    bvec, cvec, hv, vv, Gm]
  norm_num
  ring_nf
  linear_combination (-1/3 : ℝ) * ht

/-- `bᵀc = 1/2` at `σ = 3/4`. -/
lemma m1_R (t : ℝ) (ht : 192*t^3 + 96*t^2 - 1 = 0) :
    ∑ i ∈ range 6, bvec t (3/4) i * cvec t (3/4) i = 1/2 := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    bvec, cvec, hv, vv, Gm]
  norm_num
  ring_nf
  linear_combination (-1/3 : ℝ) * ht

/-- `bᵀAc = 1/6` at `σ = 1/2`. -/
lemma m2_L (t : ℝ) (ht : 192*t^3 + 96*t^2 - 1 = 0) :
    ∑ i ∈ range 6, bvec t (1/2) i * (∑ j ∈ range 6, Am t (1/2) i j * cvec t (1/2) j) = 1/6 := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    bvec, cvec, Am, hv, vv, Gm]
  norm_num
  ring_nf
  linear_combination ((-1/12 : ℝ) + (1/12 : ℝ)*t) * ht

/-- `bᵀAc = 1/6` at `σ = 3/4`. -/
lemma m2_R (t : ℝ) (ht : 192*t^3 + 96*t^2 - 1 = 0) :
    ∑ i ∈ range 6, bvec t (3/4) i * (∑ j ∈ range 6, Am t (3/4) i j * cvec t (3/4) j) = 1/6 := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    bvec, cvec, Am, hv, vv, Gm]
  norm_num
  ring_nf
  linear_combination ((-1/12 : ℝ) + (1/12 : ℝ)*t) * ht

/-! ### The three σ-independent order conditions

The key to these is to cancel `v i` *before* expanding: `b i · c i = h i · (Gv) i` and
`b i · (Ac) i = h i · (G²v) i`, after which no denominators remain and the identity is a
polynomial one modulo the cubic.  Expanding first instead leaves `field_simp` with partially
normalised inverses that `ring` cannot clear. -/

/-- `bᵀe = 1`, for every `σ` (no cubic, no denominators). -/
lemma m0_gen (t s : ℝ) : ∑ i ∈ range 6, bvec t s i = 1 := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, bvec, hv, vv]
  ring_nf

/-- `bᵀc = 1/2`, for every `σ` in the interval. -/
lemma m1_gen {t s : ℝ} (ht : 192*t^3 + 96*t^2 - 1 = 0)
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∑ i ∈ range 6, bvec t s i * cvec t s i = 1/2 := by
  obtain ⟨h1, h2⟩ := hs
  have step : ∀ i ∈ range 6, bvec t s i * cvec t s i
      = hv t i * ∑ j ∈ range 6, Gm t i j * vv s j := by
    intro i hi
    have hv0 := (vv_pos ⟨h1, h2⟩ i hi).ne'
    unfold bvec cvec
    field_simp
  rw [Finset.sum_congr rfl step]
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, hv, vv, Gm]
  ring_nf
  linear_combination (-1/3 : ℝ) * ht

/-- `bᵀAc = 1/6`, for every `σ` in the interval. -/
lemma m2_gen {t s : ℝ} (ht : 192*t^3 + 96*t^2 - 1 = 0)
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∑ i ∈ range 6, bvec t s i * (∑ j ∈ range 6, Am t s i j * cvec t s j) = 1/6 := by
  obtain ⟨h1, h2⟩ := hs
  have step : ∀ i ∈ range 6, bvec t s i * (∑ j ∈ range 6, Am t s i j * cvec t s j)
      = hv t i * ∑ j ∈ range 6, Gm t i j * (∑ k ∈ range 6, Gm t j k * vv s k) := by
    intro i hi
    have hvi := (vv_pos ⟨h1, h2⟩ i hi).ne'
    unfold bvec Am cvec
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hvj := (vv_pos ⟨h1, h2⟩ j hj).ne'
    field_simp
  rw [Finset.sum_congr rfl step]
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, hv, vv, Gm]
  ring_nf
  linear_combination ((-1/12 : ℝ) + (1/12 : ℝ)*t) * ht

/-! ## The order-three defect at the two endpoints

Along the rational line `v(s) = (21/8 − s, 17/4 + 2s, 17/4 − 2s, 7/4 + s, 1, 3/2)` the
vector `z = Bᵀ v` is **constant** (the direction `(−1, 2, −2, 1, 0, 0)` is in the kernel
of `Bᵀ`), hence `S`, `h` and `X` are constant too, and only `D = diag v` moves.  So every
condition except `bᵀc² = 1/3` holds identically in `s`, and the defect

  `defect(s) = bᵀc² − 1/3`

is the only thing that varies.  Exact computation in `ℚ(τ)` gives the two values below. -/

/-- The order-three defect at `s = 1/2`, as an element of `ℚ(τ)`. -/
noncomputable def defectL (t : ℝ) : ℝ :=
  749941919 / 44059946112 + (142212457 / 5507493264) * t
    - (5805357007 / 1376873316) * t ^ 2

/-- The order-three defect at `s = 3/4`, as an element of `ℚ(τ)`. -/
noncomputable def defectR (t : ℝ) : ℝ :=
  1087254041 / 7205666688 - (3458288341 / 4503541680) * t
    - (13337191 / 1867140) * t ^ 2

/-- **The polynomial `defectL` *is* the order-three defect of the tableau at `σ = 1/2`.**
This is the identification that was previously assumed. -/
lemma defectL_eq (t : ℝ) (ht : 192*t^3 + 96*t^2 - 1 = 0) :
    (∑ i ∈ range 6, bvec t (1/2) i * (cvec t (1/2) i)^2) - 1/3 = defectL t := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    bvec, cvec, hv, vv, Gm, defectL]
  norm_num
  ring_nf
  linear_combination ((-157636225/1074632832 : ℝ) + (-1998705391/1835831088 : ℝ)*t) * ht

/-- **The polynomial `defectR` *is* the order-three defect of the tableau at `σ = 3/4`.** -/
lemma defectR_eq (t : ℝ) (ht : 192*t^3 + 96*t^2 - 1 = 0) :
    (∑ i ∈ range 6, bvec t (3/4) i * (cvec t (3/4) i)^2) - 1/3 = defectR t := by
  simp only [show (6:ℕ)=5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    bvec, cvec, hv, vv, Gm, defectR]
  norm_num
  ring_nf
  linear_combination ((-886362751/7205666688 : ℝ) + (-5470556023/4503541680 : ℝ)*t) * ht

/-- Both defect polynomials are decreasing on the bracket, so their sign there is
determined by the value at the right end.  This is the only analytic input. -/
lemma defectL_neg_of_mem {t : ℝ} (ht : t ∈ Set.Icc (9366 / 100000 : ℝ) (9367 / 100000)) :
    defectL t < 0 := by
  obtain ⟨h1, h2⟩ := ht
  have ht0 : (0 : ℝ) < t := by linarith
  unfold defectL
  nlinarith [sq_nonneg (t - 9366 / 100000), sq_nonneg (t + 9366 / 100000), sq_nonneg t]

lemma defectR_pos_of_mem {t : ℝ} (ht : t ∈ Set.Icc (9366 / 100000 : ℝ) (9367 / 100000)) :
    0 < defectR t := by
  obtain ⟨h1, h2⟩ := ht
  have ht0 : (0 : ℝ) < t := by linarith
  unfold defectR
  nlinarith [sq_nonneg (t - 9366 / 100000), sq_nonneg (t + 9366 / 100000), sq_nonneg t]

/-- **The defect changes sign.**  At the parameter `τ` the two endpoint values of the
order-three defect have strictly opposite signs. -/
theorem defect_sign_change :
    ∃ τ : ℝ, cub τ = 0 ∧ τ ∈ Set.Ioo (9366 / 100000 : ℝ) (9367 / 100000) ∧
      defectL τ < 0 ∧ 0 < defectR τ := by
  obtain ⟨τ, hmem, h0⟩ := tau_exists
  have hIcc : τ ∈ Set.Icc (9366 / 100000 : ℝ) (9367 / 100000) :=
    Set.mem_Icc.2 ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  exact ⟨τ, h0, hmem, defectL_neg_of_mem hIcc, defectR_pos_of_mem hIcc⟩

/-- **The order-three condition is attained.**  Any continuous interpolation of the
defect between the two endpoints vanishes somewhere strictly inside.  Applied to
`s ↦ bᵀc²(s) − 1/3` this produces the parameter at which the counterexample lives. -/
theorem six_stage_defect_root (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (1/2 : ℝ) (3/4)))
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (9366 / 100000 : ℝ) (9367 / 100000))
    (hfL : f (1/2) = defectL τ) (hfR : f (3/4) = defectR τ) :
    ∃ σ ∈ Set.Ioo (1/2 : ℝ) (3/4), f σ = 0 := by
  have hIcc : τ ∈ Set.Icc (9366 / 100000 : ℝ) (9367 / 100000) :=
    Set.mem_Icc.2 ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have hmem : (0 : ℝ) ∈ Set.Ioo (f (1/2)) (f (3/4)) := by
    rw [hfL, hfR]
    exact Set.mem_Ioo.2 ⟨defectL_neg_of_mem hIcc, defectR_pos_of_mem hIcc⟩
  obtain ⟨σ, hσ, h0⟩ :=
    intermediate_value_Ioo (by norm_num : (1/2 : ℝ) ≤ 3/4) hf hmem
  exact ⟨σ, hσ, h0⟩


/-! ## The order-three condition, attained by the tableau

The defect is now identified with the two polynomials (`defectL_eq`, `defectR_eq`), so the
sign change applies to the tableau itself rather than to an assumed interpolant. -/

/-- The order-three defect as a function of the line parameter. -/
noncomputable def defect (t s : ℝ) : ℝ :=
  (∑ i ∈ range 6, bvec t s i * (cvec t s i) ^ 2) - 1/3

/-- Each coordinate of `v` is continuous in `σ`. -/
lemma vv_cont (i : ℕ) : Continuous (fun s => vv s i) := by
  match i with
  | 0 => simp only [vv]; fun_prop
  | 1 => simp only [vv]; fun_prop
  | 2 => simp only [vv]; fun_prop
  | 3 => simp only [vv]; fun_prop
  | 4 => simp only [vv]; fun_prop
  | 5 => simp only [vv]; fun_prop
  | (n+6) => simp only [vv]; fun_prop

/-- The defect is continuous on the parameter interval: the only denominators are the
`v i(σ)`, which are positive there. -/
lemma defect_cont (t : ℝ) : ContinuousOn (defect t) (Set.Icc (1/2 : ℝ) (3/4)) := by
  unfold defect cvec bvec
  apply ContinuousOn.sub _ continuousOn_const
  apply continuousOn_finsetSum
  intro i hi
  apply ContinuousOn.mul
  · exact ((vv_cont i).continuousOn).mul continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.div
    · apply continuousOn_finsetSum
      intro j _
      exact continuousOn_const.mul ((vv_cont j).continuousOn)
    · exact (vv_cont i).continuousOn
    · intro s hs
      exact (vv_pos hs i hi).ne'

/-- **The order-three condition is attained by the tableau itself.**  Combined with
`uniform_conditions` this makes all eleven conditions of the Claim hold simultaneously. -/
theorem defect_has_root {t : ℝ} (htc : 192*t^3 + 96*t^2 - 1 = 0)
    (ht : t ∈ Set.Ioo (9366/100000 : ℝ) (9367/100000)) :
    ∃ s ∈ Set.Ioo (1/2 : ℝ) (3/4),
      ∑ i ∈ range 6, bvec t s i * (cvec t s i) ^ 2 = 1/3 := by
  have hIcc : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000) :=
    Set.mem_Icc.2 ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hL : defect t (1/2) < 0 := by
    rw [show defect t (1/2) = defectL t from defectL_eq t htc]
    exact defectL_neg_of_mem hIcc
  have hR : 0 < defect t (3/4) := by
    rw [show defect t (3/4) = defectR t from defectR_eq t htc]
    exact defectR_pos_of_mem hIcc
  obtain ⟨s, hs, h0⟩ := intermediate_value_Ioo (by norm_num : (1/2:ℝ) ≤ 3/4)
    (defect_cont t) (Set.mem_Ioo.2 ⟨hL, hR⟩)
  refine ⟨s, hs, ?_⟩
  unfold defect at h0
  linarith

/-! ## The refutation

Everything is now in place: `uniform_conditions` gives the structural conditions at every
parameter value, `m0_gen`/`m1_gen`/`m2_gen` give three of the four order conditions, and
`defect_has_root` supplies a parameter at which the fourth holds. -/

/-- **The Claim is false: an unconditional six-stage counterexample.**

There are a cubic parameter `t` and a line parameter `s` for which the tableau
`A = D⁻¹GD`, `b = Dh`, `R = DXD`, `c = Ae` satisfies *every* hypothesis of the Claim —
`A ≥ 0`, `b > 0`, `c = Ae` strictly increasing after the fixed relabelling `perm` with
entries in `(0,1)`, `R` symmetric positive semidefinite with `Re = b`, and all four order
conditions `bᵀe = 1`, `bᵀc = 1/2`, `bᵀAc = 1/6`, `bᵀc² = 1/3` — while

  `M = R A + Aᵀ R − b bᵀ = 0`,

so `M` is positive semidefinite.  The Claim asserts this is impossible. -/
theorem claim_is_false :
    ∃ t s : ℝ, (192*t^3 + 96*t^2 - 1 = 0)
      ∧ (∀ i j, 0 ≤ Am t s (perm i) (perm j))
      ∧ (∀ i ∈ range 6, 0 < bvec t s i)
      ∧ (∀ i ∈ range 6, cvec t s i = ∑ j ∈ range 6, Am t s i j)
      ∧ (∀ i ∈ range 6, 0 < cvec t s i ∧ cvec t s i < 1)
      ∧ (∀ i ∈ range 6, ∀ j ∈ range 6, i < j → cvec t s (perm i) < cvec t s (perm j))
      ∧ (∀ i ∈ range 6, ∀ j ∈ range 6, Rm t s i j = Rm t s j i)
      ∧ (∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 6, ∑ j ∈ range 6, Rm t s i j * (x i * x j))
      ∧ (∀ i ∈ range 6, ∑ j ∈ range 6, Rm t s i j = bvec t s i)
      ∧ (∑ i ∈ range 6, bvec t s i = 1)
      ∧ (∑ i ∈ range 6, bvec t s i * cvec t s i = 1/2)
      ∧ (∑ i ∈ range 6, bvec t s i * (∑ j ∈ range 6, Am t s i j * cvec t s j) = 1/6)
      ∧ (∑ i ∈ range 6, bvec t s i * (cvec t s i)^2 = 1/3)
      ∧ (∀ i ∈ range 6, ∀ j ∈ range 6,
          (∑ k ∈ range 6, Rm t s i k * Am t s k j)
            + (∑ k ∈ range 6, Rm t s j k * Am t s k i)
            - bvec t s i * bvec t s j = 0) := by
  obtain ⟨t, htmem, htc⟩ := tau_exists
  have hcub : 192*t^3 + 96*t^2 - 1 = 0 := by unfold cub at htc; linarith
  obtain ⟨s, hsmem, h4⟩ := defect_has_root hcub htmem
  have hIcc : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  have hsIcc : s ∈ Set.Icc (1/2 : ℝ) (3/4) :=
    Set.mem_Icc.2 ⟨le_of_lt hsmem.1, le_of_lt hsmem.2⟩
  have ht0 : (0:ℝ) < t := by have := hIcc.1; linarith
  obtain ⟨_, hb, hc, hcr, _, hRs, hRp, hRe, hM⟩ := uniform_conditions hcub hIcc hsIcc
  exact ⟨t, s, hcub, Am_nonneg_all ht0 hsIcc, hb, hc, hcr,
    cvec_perm_mono hIcc hsIcc, hRs, hRp, hRe,
    m0_gen t s, m1_gen hcub hsIcc, m2_gen hcub hsIcc, h4, hM⟩

/-! ## The `AlgStabData 6` instance

`SSPLean/AlgStabCounterexample.lean` bundles the hypotheses of the Claim as
`AlgStabData s`, so that an inhabitant *is* a counterexample.  `claim_is_false` supplies
everything needed, but in the original stage order; `AlgStabData` additionally wants `c`
increasing in the index and `A ≥ 0` for all of `ℕ`.  We therefore relabel by `perm` and
check that each field transfers. -/

/-- The inverse of `perm` on `range 6`. -/
def iperm : ℕ → ℕ := fun k =>
  match k with
  | 3 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 5 => 4 | 0 => 5 | _ => 6

lemma iperm_perm : ∀ i ∈ range 6, iperm (perm i) = i := by
  intro i hi
  have := mem_range.1 hi
  interval_cases i <;> rfl

/-- Reindexing a double sum by `perm`. -/
lemma sum_perm2 (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ range 6, ∑ j ∈ range 6, f (perm i) (perm j)
      = ∑ i ∈ range 6, ∑ j ∈ range 6, f i j := by
  rw [sum_perm (fun i => ∑ j ∈ range 6, f i (perm j))]
  exact Finset.sum_congr rfl fun i _ => sum_perm (fun j => f i j)

/-! ### The relabelled tableau -/

/-- Relabelled coefficient matrix. -/
noncomputable def Ap (t s : ℝ) : ℕ → ℕ → ℝ := fun i j => Am t s (perm i) (perm j)

/-- Relabelled weights. -/
noncomputable def bp (t s : ℝ) : ℕ → ℝ := fun i => bvec t s (perm i)

/-- Relabelled certificate. -/
noncomputable def Rp (t s : ℝ) : ℕ → ℕ → ℝ := fun i j => Rm t s (perm i) (perm j)

/-- Relabelled abscissas. -/
noncomputable def cp (t s : ℝ) : ℕ → ℝ := fun i => cvec t s (perm i)

lemma Ap_rowsum (t s : ℝ) (i : ℕ) :
    ∑ j ∈ range 6, Ap t s i j = ∑ j ∈ range 6, Am t s (perm i) j :=
  sum_perm (fun j => Am t s (perm i) j)

lemma Rp_rowsum (t s : ℝ) (i : ℕ) :
    ∑ j ∈ range 6, Rp t s i j = ∑ j ∈ range 6, Rm t s (perm i) j :=
  sum_perm (fun j => Rm t s (perm i) j)

lemma cp_rowsum (t s : ℝ) : ∀ i ∈ range 6, cp t s i = ∑ j ∈ range 6, Ap t s i j := by
  intro i hi
  rw [Ap_rowsum]
  exact cvec_eq_rowsum t s (perm i) (perm_mem i hi)

lemma Rp_eq_bp (t s : ℝ) : ∀ i ∈ range 6, bp t s i = ∑ j ∈ range 6, Rp t s i j := by
  intro i hi
  rw [Rp_rowsum]
  exact (Rm_rowsum t s (perm i) (perm_mem i hi)).symm

lemma Rp_symm (t s : ℝ) : SymmOn 6 (Rp t s) := by
  intro i hi j hj
  unfold Rp
  exact Rm_symm t s (perm i) (perm_mem i hi) (perm j) (perm_mem j hj)

lemma Rp_psd {t : ℝ} (ht : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000)) (s : ℝ) :
    PSDOn 6 (Rp t s) := by
  intro x
  have h : ∑ i ∈ range 6, ∑ j ∈ range 6, Rp t s i j * (x i * x j)
      = ∑ i ∈ range 6, ∑ j ∈ range 6,
          Rm t s i j * ((fun k => x (iperm k)) i * (fun k => x (iperm k)) j) := by
    rw [← sum_perm2 (fun i j => Rm t s i j * (x (iperm i) * x (iperm j)))]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    unfold Rp
    rw [iperm_perm i hi, iperm_perm j hj]
  rw [h]
  exact Rm_psd ht s _

lemma Mp_inner (t s : ℝ) (i j : ℕ) :
    ∑ k ∈ range 6, Rp t s i k * Ap t s k j
      = ∑ k ∈ range 6, Rm t s (perm i) k * Am t s k (perm j) :=
  sum_perm (fun k => Rm t s (perm i) k * Am t s k (perm j))

lemma Mp_zero {t s : ℝ} (htc : 192*t^3 + 96*t^2 - 1 = 0)
    (hs : s ∈ Set.Icc (1/2 : ℝ) (3/4)) :
    ∀ i ∈ range 6, ∀ j ∈ range 6,
      (∑ k ∈ range 6, Rp t s i k * Ap t s k j)
        + (∑ k ∈ range 6, Rp t s j k * Ap t s k i) - bp t s i * bp t s j = 0 := by
  intro i hi j hj
  rw [Mp_inner, Mp_inner]
  unfold bp
  exact Mm_zero htc hs (perm i) (perm_mem i hi) (perm j) (perm_mem j hj)

lemma bp_sum (t s : ℝ) : ∑ i ∈ range 6, bp t s i = ∑ i ∈ range 6, bvec t s i :=
  sum_perm (fun i => bvec t s i)

lemma bp_cp_sum (t s : ℝ) :
    ∑ i ∈ range 6, bp t s i * cp t s i = ∑ i ∈ range 6, bvec t s i * cvec t s i :=
  sum_perm (fun i => bvec t s i * cvec t s i)

lemma bp_cp2_sum (t s : ℝ) :
    ∑ i ∈ range 6, bp t s i * (cp t s i)^2 = ∑ i ∈ range 6, bvec t s i * (cvec t s i)^2 :=
  sum_perm (fun i => bvec t s i * (cvec t s i)^2)

lemma bp_Ap_cp_sum (t s : ℝ) :
    ∑ i ∈ range 6, bp t s i * ∑ j ∈ range 6, Ap t s i j * cp t s j
      = ∑ i ∈ range 6, bvec t s i * ∑ j ∈ range 6, Am t s i j * cvec t s j := by
  have inner : ∀ i, ∑ j ∈ range 6, Ap t s i j * cp t s j
      = ∑ j ∈ range 6, Am t s (perm i) j * cvec t s j := by
    intro i
    unfold Ap cp
    exact sum_perm (fun j => Am t s (perm i) j * cvec t s j)
  calc ∑ i ∈ range 6, bp t s i * ∑ j ∈ range 6, Ap t s i j * cp t s j
      = ∑ i ∈ range 6, bvec t s (perm i) * ∑ j ∈ range 6, Am t s (perm i) j * cvec t s j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner i]; rfl
    _ = ∑ i ∈ range 6, bvec t s i * ∑ j ∈ range 6, Am t s i j * cvec t s j :=
        sum_perm (fun i => bvec t s i * ∑ j ∈ range 6, Am t s i j * cvec t s j)

/-- **`AlgStabData 6` is inhabited.**

This is the corollary that lands the six-stage counterexample in the framework of
`SSPLean/AlgStabCounterexample.lean`: an inhabitant of `AlgStabData 6` is by definition a
tableau meeting every hypothesis of the Claim with `M = 0`.  Consequently
`SSP.Counterexample.claim_false` and `SSP.Counterexample.R_not_diagonal` apply to it —
in particular the certificate is necessarily non-diagonal, consistent with the
diagonal-`R` barrier of `SSPLean/BStability.lean`. -/
theorem algStabData_six_nonempty : Nonempty (AlgStabData 6) := by
  obtain ⟨t, htmem, htc⟩ := tau_exists
  have hcub : 192*t^3 + 96*t^2 - 1 = 0 := by unfold cub at htc; linarith
  obtain ⟨s, hsmem, h4⟩ := defect_has_root hcub htmem
  have hIcc : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  have hsIcc : s ∈ Set.Icc (1/2 : ℝ) (3/4) :=
    Set.mem_Icc.2 ⟨le_of_lt hsmem.1, le_of_lt hsmem.2⟩
  have ht0 : (0:ℝ) < t := by have := hIcc.1; linarith
  refine ⟨{
    A := Ap t s
    b := bp t s
    R := Rp t s
    c := cp t s
    hA := Am_nonneg_all ht0 hsIcc
    hb := fun i hi => bvec_pos hIcc hsIcc (perm i) (perm_mem i hi)
    hc := cp_rowsum t s
    hcmono := cvec_perm_mono hIcc hsIcc
    hcrange := fun i hi => ?_
    hRsymm := Rp_symm t s
    hRpsd := Rp_psd hIcc s
    hRe := Rp_eq_bp t s
    h1 := ?_
    h2 := ?_
    h3 := ?_
    h4 := ?_
    hM := Mp_zero hcub hsIcc }⟩
  · exact ⟨le_of_lt (cvec_mem hIcc hsIcc (perm i) (perm_mem i hi)).1,
      le_of_lt (cvec_mem hIcc hsIcc (perm i) (perm_mem i hi)).2⟩
  · rw [bp_sum]; exact m0_gen t s
  · rw [bp_cp_sum]; exact m1_gen hcub hsIcc
  · rw [bp_Ap_cp_sum]; exact m2_gen hcub hsIcc
  · rw [bp_cp2_sum]; exact h4

/-! ### Consequences in the framework of `AlgStabCounterexample.lean`

The results there are stated conditionally on an inhabitant of `AlgStabData s`; with
`algStabData_six_nonempty` they become unconditional at `s = 6`. -/

/-- **The algebraic-stability matrix of a genuine counterexample is positive semidefinite.**
This is `SSP.Counterexample.claim_false` with its hypothesis discharged: the Claim asserts
this configuration is impossible. -/
theorem exists_psd_M :
    ∃ d : AlgStabData 6, PSDOn 6 (fun i j =>
      (∑ k ∈ range 6, d.R i k * d.A k j)
        + (∑ k ∈ range 6, d.R j k * d.A k i) - d.b i * d.b j) := by
  obtain ⟨d⟩ := algStabData_six_nonempty
  exact ⟨d, d.M_psd⟩

/-- **The certificate is necessarily non-diagonal**, by `R_not_diagonal`.  So the
counterexample does not contradict the diagonal-`R` barrier
`SSP.no_order3_algebraically_stable` of `SSPLean/BStability.lean`: the two live in
different regimes, which is exactly the gap in the Claim. -/
theorem exists_nondiagonal_certificate : ∃ d : AlgStabData 6, ¬ DiagOn 6 d.R := by
  obtain ⟨d⟩ := algStabData_six_nonempty
  exact ⟨d, R_not_diagonal d⟩

/-! ## Counterexamples at every stage count `≥ 6`

Combining the six-stage witness with the padding step: the Claim (with its own hypothesis
`b ≥ 0`) fails at *every* stage count from `6` upwards. -/

/-- The six-stage witness, with the strict bound `c < 1` that leaves room for padding. -/
theorem six_strictWeak_nonempty : Nonempty (StrictWeak 6) := by
  obtain ⟨t, htmem, htc⟩ := tau_exists
  have hcub : 192*t^3 + 96*t^2 - 1 = 0 := by unfold cub at htc; linarith
  obtain ⟨s, hsmem, h4⟩ := defect_has_root hcub htmem
  have hIcc : t ∈ Set.Icc (9366/100000 : ℝ) (9367/100000) :=
    Set.mem_Icc.2 ⟨le_of_lt htmem.1, le_of_lt htmem.2⟩
  have hsIcc : s ∈ Set.Icc (1/2 : ℝ) (3/4) :=
    Set.mem_Icc.2 ⟨le_of_lt hsmem.1, le_of_lt hsmem.2⟩
  have ht0 : (0:ℝ) < t := by have := hIcc.1; linarith
  refine ⟨{
    data :=
      { A := Ap t s
        b := bp t s
        R := Rp t s
        c := cp t s
        hA := Am_nonneg_all ht0 hsIcc
        hb := fun i hi => (bvec_pos hIcc hsIcc (perm i) (perm_mem i hi)).le
        hc := cp_rowsum t s
        hcmono := cvec_perm_mono hIcc hsIcc
        hcrange := fun i hi =>
          ⟨le_of_lt (cvec_mem hIcc hsIcc (perm i) (perm_mem i hi)).1,
           le_of_lt (cvec_mem hIcc hsIcc (perm i) (perm_mem i hi)).2⟩
        hRsymm := Rp_symm t s
        hRpsd := Rp_psd hIcc s
        hRe := Rp_eq_bp t s
        h1 := by rw [bp_sum]; exact m0_gen t s
        h2 := by rw [bp_cp_sum]; exact m1_gen hcub hsIcc
        h3 := by rw [bp_Ap_cp_sum]; exact m2_gen hcub hsIcc
        h4 := by rw [bp_cp2_sum]; exact h4
        hM := Mp_zero hcub hsIcc }
    hlt1 := fun i hi => (cvec_mem hIcc hsIcc (perm i) (perm_mem i hi)).2 }⟩

/-- **The Claim fails at every stage count `≥ 6`.**

For each `n` there is a `(6+n)`-stage tableau satisfying every hypothesis of the Claim —
with the Claim's own weight condition `b ≥ 0` — while `M = R A + Aᵀ R − b bᵀ = 0`.  The
witnesses for `n ≥ 1` carry `n` zero-weight stages; by the discussion above that is
unavoidable for any padding argument. -/
theorem weak_counterexample_all_stages : ∀ n, Nonempty (WeakAlgStabData (6 + n)) := by
  intro n
  obtain ⟨w⟩ := six_strictWeak_nonempty
  obtain ⟨wn⟩ := w.exists_all n
  exact ⟨wn.data⟩

/-- The same, indexed by a stage count `s ≥ 6`. -/
theorem weak_counterexample_of_ge {s : ℕ} (hs : 6 ≤ s) : Nonempty (WeakAlgStabData s) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact weak_counterexample_all_stages n

/-- **The Claim is false at every stage count `≥ 6`.**  For each such `s` there is a tableau
meeting all of the Claim's hypotheses (with its own `b ≥ 0`) whose algebraic-stability matrix
is positive semidefinite — indeed identically zero. -/
theorem claim_false_all_stages {s : ℕ} (hs : 6 ≤ s) :
    ∃ d : WeakAlgStabData s, PSDOn s (fun i j =>
      (∑ k ∈ range s, d.R i k * d.A k j)
        + (∑ k ∈ range s, d.R j k * d.A k i) - d.b i * d.b j) := by
  obtain ⟨d⟩ := weak_counterexample_of_ge hs
  exact ⟨d, d.M_psd⟩

end Six

end Counterexample

end SSP
