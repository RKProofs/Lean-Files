import SSPLean.TwoStageClaim

/-!
# A block reduction at four stages, and the support-two obstruction

This file records what the two-stage theorem buys at four stages.

The four-stage case is the only one left open: the Claim is inconsistent at `s = 2`
(`SSP.TwoStage.two_stage_claim_inconsistent`) and at `s = 3`
(`SSP.ThreeStage.three_stage_claim_inconsistent`), and explicit counterexamples exist for every
`s ≥ 5`.  The obstruction at `s = 4` is that the weight vector `b` may vanish at two indices
(`b` needs support only of size `≥ 2`), and the four moment conditions are then *blind* to the
rows of `A` indexed by the vanishing set: `bᵗAc` involves only the rows in `supp b`.  So only
`M ⪰ 0` can constrain them, and `M ⪰ 0` bounds a trace from below, never from above.

What is proved here is that once the two blocks *decouple*, the surviving block is a two-stage
solution, which is impossible.  Precisely, write `S = supp b` and `Z` for its complement, and
suppose

* `A i j = 0` for `i ∈ S`, `j ∈ Z` — the supported rows carry no mass in the `Z` columns;
* `K|_{S,Z} e = 0`, i.e. `K i 2 + K i 3 = 0` for `i ∈ S`, where `K = R − bbᵗ`;
* `K|_{S,Z} · A|_{Z,S} = 0` entrywise.

The last two are strictly weaker than `K|_{S,Z} = 0`: the first is only what is needed for
`R|S e = b|S`, and the second only for the cross term in `M|S` to vanish.

Then `(A|S, R|S, b|S, c|S)` satisfies every hypothesis of `Data2` and `Rdiag` applies, so no
such configuration exists.  Two points are worth noting.

* The block `A|_{Z×S}` is left completely **free**: it never enters the `S`-block of `M` once
  the `K` block vanishes.  Only the `(S,Z)` blocks of `A` and `K` must vanish.
* The hypotheses on `K` are strictly weaker than `Re_k = 0`.  The unified note deletes a
  *single* zero-weight index under `Ke_k = 0` (which forces the whole `k`-th row and column of
  `R` to vanish) and lands at `s = 3`.  Deleting *two* indices lands at `s = 2`, which is
  available only now that the two-stage case is proved.
* `A|_{S,Z} = 0` is **forced**, not assumed, whenever the kernel eigenline contains a
  nonnegative vector with full `Z`-support — see `AZ_eq_zero_of_pos_kernel`.  That is exactly
  the configuration the unified note's `lem:rank2zsign` leaves uncovered: its proof concludes
  that a nonnegative `z ∈ N₀` is a multiple of a single `e_k` by citing the three-stage fact
  that at most one weight vanishes, and that fact is `s = 3`-only (two vanishing weights at
  `s = 4` leave a support of size two, which is feasible).

The hypotheses are not vacuous.  Dropping only the moment conditions, one may take

  `b = (1/2, 1/2, 0, 0)`,  `A = diag(1/2, 1/2, 5, 7)`,  `K = 0`  (so `R = bbᵗ`),

for which `A ≥ 0`, `R ⪰ 0`, `Re = b`, `c = Ae = (1/2, 1/2, 5, 7)`, both `(S,Z)` blocks vanish,
and `M = 0 ⪰ 0` exactly — because `Aᵗb = b/2` makes `bηᵗ + ηbᵗ − bbᵗ` vanish.  Here `θ = 13`,
which illustrates the point of the file: with `b` vanishing on `Z`, the trace is unbounded and
`M ⪰ 0` does nothing to stop it.  What fails for this configuration is the moment conditions
(`bᵗc² = 1/4 ≠ 1/3`), and the theorem says that is not a coincidence.

## Main results

* `Data2.ofBlock` — the reduction: a four-stage configuration with decoupled blocks and
  `|supp b| = 2` yields a `Data2`
* `four_stage_block_impossible` — hence no such configuration exists
* `AZ_eq_zero_of_pos_kernel` — `A|_{S,Z} = 0` is forced by a positive kernel direction on `Z`
* `four_stage_block_impossible_of_pos_kernel` — the two combined

## What this does *not* settle

The general `s = 4` case remains open.  What is still needed is `K|_{S,Z} A|_{Z,S} = 0`.  In
the forced situation above one gets more structure than is used here: `K z = 0` makes both
`K|_{Z,Z}` and `K|_{S,Z}` multiples of `v = (z 3, −z 2)ᵗ` in their `Z` index, so
`K|_{S,Z} = u vᵗ` for some `u`, and the cross term becomes `u wᵗ + w uᵗ` with
`w = (A|_{Z,S})ᵗ v` — a matrix of determinant `−(u₁w₂ − u₂w₁)² ≤ 0`, the same shape as in
`SSP.ThreeStage.rank_one_eigen`.  Since that matrix is not positive semidefinite, `M|S ⪰ 0`
does not by itself give the two-stage form, and closing the case needs an argument that
`u wᵗ + w uᵗ` cannot rescue an otherwise infeasible `M|S`.  The unified note's rank-two and
rank-three branches with `M ≠ 0` and `b > 0` are untouched by this file.
-/

open Finset

namespace SSP.FourStage

/-- The four-stage hypotheses of the Claim, bundled.  Identical to `SSP.ThreeStage.Data` and
`SSP.TwoStage.Data2` with `range 4` in place of `range 3`, `range 2`. -/
structure Data4 where
  A : ℕ → ℕ → ℝ
  R : ℕ → ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ
  hA : ∀ i ∈ range 4, ∀ j ∈ range 4, 0 ≤ A i j
  hRsymm : ∀ i ∈ range 4, ∀ j ∈ range 4, R i j = R j i
  hRpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 4, ∑ j ∈ range 4, R i j * (x i * x j)
  hb : ∀ i ∈ range 4, b i = ∑ j ∈ range 4, R i j
  hbnn : ∀ i ∈ range 4, 0 ≤ b i
  hc : ∀ i ∈ range 4, c i = ∑ j ∈ range 4, A i j
  hMpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range 4, ∑ j ∈ range 4,
    ((∑ k ∈ range 4, R i k * A k j) + (∑ k ∈ range 4, R j k * A k i) - b i * b j) * (x i * x j)
  h1 : ∑ i ∈ range 4, b i = 1
  h2 : ∑ i ∈ range 4, b i * c i = 1/2
  h3 : ∑ i ∈ range 4, b i * (c i)^2 = 1/3
  h4 : ∑ i ∈ range 4, b i * ∑ j ∈ range 4, A i j * c j = 1/6

variable (d : Data4)

/-- Expand a four-term sum. -/
lemma sum4 (f : ℕ → ℝ) : ∑ i ∈ range 4, f i = f 0 + f 1 + f 2 + f 3 := by
  simp only [show (4:ℕ)=3+1 from rfl, show (3:ℕ)=2+1 from rfl, show (2:ℕ)=1+1 from rfl,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- `K = R − bbᵗ`. -/
noncomputable def Km4 : ℕ → ℕ → ℝ := fun i j => d.R i j - d.b i * d.b j

/-! ## The reduction

We take the vanishing set to be `Z = {2, 3}` and the support to be `S = {0, 1}`; any other
two-element support is handled by relabelling, exactly as at three stages.
-/

/-- **The block reduction.**  A four-stage configuration whose weight vector is supported on
`{0,1}` and whose `(S,Z)` blocks of `A` and `K` vanish restricts to a two-stage configuration.

Every hypothesis transfers:

* `A|S ≥ 0`, `R|S` symmetric, and `R|S ⪰ 0`, `M|S ⪰ 0` as principal submatrices;
* `(Ae)|S = A|S e` and `(Ke)|S = K|S e` because the `(S,Z)` blocks vanish, and the latter gives
  `R|S e = b|S` using `bᵗe = 1`;
* `M|S = R|S A|S + A|Sᵗ R|S − b|S b|Sᵗ` exactly — this is where `K i j = 0` for `i ∈ S`,
  `j ∈ Z` is used, and it is what leaves `A|_{Z×S}` free;
* all four moment conditions restrict unchanged, since `b` vanishes on `Z`. -/
noncomputable def Data2.ofBlock
    (hb2 : d.b 2 = 0) (hb3 : d.b 3 = 0)
    (hAZ : ∀ i ∈ range 2, ∀ j ∈ ({2, 3} : Finset ℕ), d.A i j = 0)
    (hKe : ∀ i ∈ range 2, Km4 d i 2 + Km4 d i 3 = 0)
    (hKA : ∀ i ∈ range 2, ∀ j ∈ range 2,
      Km4 d i 2 * d.A 2 j + Km4 d i 3 * d.A 3 j = 0) :
    SSP.TwoStage.Data2 where
  A := d.A
  R := d.R
  b := d.b
  c := d.c
  hA := fun i hi j hj => d.hA i (by
      have := mem_range.1 hi; exact mem_range.2 (by omega)) j (by
      have := mem_range.1 hj; exact mem_range.2 (by omega))
  hRsymm := fun i hi j hj => d.hRsymm i (by
      have := mem_range.1 hi; exact mem_range.2 (by omega)) j (by
      have := mem_range.1 hj; exact mem_range.2 (by omega))
  hRpsd := fun x => by
    -- `R|S` is a principal submatrix of `R`: test `R` at the extension of `x` by zero
    have h := d.hRpsd (fun i => if i < 2 then x i else 0)
    simp only [sum4, SSP.TwoStage.sum2] at h ⊢
    norm_num at h
    linarith [h]
  hb := fun i hi => by
    -- `R|S e = b|S`: the `Z`-columns of `R` contribute `K i 2 + K i 3 = 0` to row `i`
    have hi' := mem_range.1 hi
    have hK := hKe i hi
    have hbi := d.hb i (by exact mem_range.2 (by omega))
    rw [sum4] at hbi
    simp only [Km4] at hK
    rw [hb2, hb3] at hK
    simp only [SSP.TwoStage.sum2]
    linarith
  hbnn := fun i hi => d.hbnn i (by
      have := mem_range.1 hi; exact mem_range.2 (by omega))
  hc := fun i hi => by
    -- `(Ae)|S = A|S e`, from the vanishing `(S,Z)` block of `A`
    have hi' := mem_range.1 hi
    have hA' := hAZ i hi
    have a2 := hA' 2 (by simp)
    have a3 := hA' 3 (by simp)
    have hci := d.hc i (by exact mem_range.2 (by omega))
    rw [sum4] at hci
    simp only [SSP.TwoStage.sum2]
    rw [a2, a3] at hci
    linarith
  hMpsd := fun x => by
    -- `M|S` is the principal submatrix; the cross term it picks up is
    -- `K|_{S,Z} A|_{Z,S} + (…)ᵗ`, which `hKA` kills entrywise
    have h := d.hMpsd (fun i => if i < 2 then x i else 0)
    have q00 := (hKA 0 (by simp)) 0 (by simp)
    have q01 := (hKA 0 (by simp)) 1 (by simp)
    have q10 := (hKA 1 (by simp)) 0 (by simp)
    have q11 := (hKA 1 (by simp)) 1 (by simp)
    simp only [Km4] at q00 q01 q10 q11
    rw [hb2, hb3] at q00 q01 q10 q11
    simp only [sum4, SSP.TwoStage.sum2] at h ⊢
    norm_num at h q00 q01 q10 q11
    -- the four `q` identities cancel the cross term exactly; state that as an equality
    -- of the two forms and rewrite
    have key : ∑ i ∈ range 2, ∑ j ∈ range 2,
        ((∑ k ∈ range 2, d.R i k * d.A k j) + (∑ k ∈ range 2, d.R j k * d.A k i)
          - d.b i * d.b j) * (x i * x j)
        = ∑ i ∈ range 4, ∑ j ∈ range 4,
        ((∑ k ∈ range 4, d.R i k * d.A k j) + (∑ k ∈ range 4, d.R j k * d.A k i)
          - d.b i * d.b j)
          * ((fun i => if i < 2 then x i else 0) i * (fun i => if i < 2 then x i else 0) j) := by
      simp only [sum4, SSP.TwoStage.sum2]
      norm_num
      linear_combination (-2 * (x 0)^2) * q00 + (-2 * x 0 * x 1) * q01
        + (-2 * x 0 * x 1) * q10 + (-2 * (x 1)^2) * q11
    simp only [sum4, SSP.TwoStage.sum2] at key
    norm_num at key
    rw [key]
    exact h
  h1 := by
    have h := d.h1; rw [sum4] at h; simp only [SSP.TwoStage.sum2]
    rw [hb2, hb3] at h; linarith
  h2 := by
    have h := d.h2; rw [sum4] at h; simp only [SSP.TwoStage.sum2]
    rw [hb2, hb3] at h; linarith
  h3 := by
    have h := d.h3; rw [sum4] at h; simp only [SSP.TwoStage.sum2]
    rw [hb2, hb3] at h; linarith
  h4 := by
    have h := d.h4
    have a02 := (hAZ 0 (by simp)) 2 (by simp)
    have a03 := (hAZ 0 (by simp)) 3 (by simp)
    have a12 := (hAZ 1 (by simp)) 2 (by simp)
    have a13 := (hAZ 1 (by simp)) 3 (by simp)
    simp only [sum4] at h
    simp only [SSP.TwoStage.sum2]
    rw [hb2, hb3] at h
    rw [a02, a03, a12, a13] at h
    linarith

/-- **No four-stage configuration with decoupled blocks exists.**

Combining `Data2.ofBlock` with the two-stage theorem.  Note that the block
`A|_{Z×S}` — the entries `A i j` with `i ∈ {2,3}`, `j ∈ {0,1}` — is unconstrained by the
hypotheses, as is the whole `Z × Z` block; the reduction does not see them. -/
theorem four_stage_block_impossible
    (hb2 : d.b 2 = 0) (hb3 : d.b 3 = 0)
    (hAZ : ∀ i ∈ range 2, ∀ j ∈ ({2, 3} : Finset ℕ), d.A i j = 0)
    (hKe : ∀ i ∈ range 2, Km4 d i 2 + Km4 d i 3 = 0)
    (hKA : ∀ i ∈ range 2, ∀ j ∈ range 2,
      Km4 d i 2 * d.A 2 j + Km4 d i 3 * d.A 3 j = 0) :
    False :=
  SSP.TwoStage.two_stage_claim_inconsistent ⟨Data2.ofBlock d hb2 hb3 hAZ hKe hKA⟩

/-! ## When the block hypotheses are forced

The hypothesis `A|_{S,Z} = 0` is not an extra assumption in the situation that actually arises.
Suppose the eigenline `N₀ = ker K ∩ b^⊥` contains a *nonnegative* vector `z` whose support is
all of `Z` — the configuration the unified note's `lem:rank2zsign` does not cover, because its
proof invokes the three-stage fact that at most one weight vanishes.  Then `A z = α z` and
`z i = 0` for `i ∈ S` force, for each `i ∈ S`,

  `A i 2 * z 2 + A i 3 * z 3 = 0`,

and since `A ≥ 0` with `z 2, z 3 > 0` every term vanishes: `A|_{S,Z} = 0`. -/

/-- **`A|_{S,Z} = 0` is forced** by a strictly positive kernel direction on `Z`.  Nonnegativity
of `A` turns the eigen-relation into a sum of nonnegative terms that must vanish. -/
lemma AZ_eq_zero_of_pos_kernel
    (z2 z3 : ℝ) (hz2 : 0 < z2) (hz3 : 0 < z3)
    (hAz : ∀ i ∈ range 2, d.A i 2 * z2 + d.A i 3 * z3 = 0) :
    ∀ i ∈ range 2, ∀ j ∈ ({2, 3} : Finset ℕ), d.A i j = 0 := by
  intro i hi j hj
  have hi' := mem_range.1 hi
  have h := hAz i hi
  have h2 : 0 ≤ d.A i 2 := d.hA i (mem_range.2 (by omega)) 2 (by simp)
  have h3 : 0 ≤ d.A i 3 := d.hA i (mem_range.2 (by omega)) 3 (by simp)
  have t2 : 0 ≤ d.A i 2 * z2 := mul_nonneg h2 (le_of_lt hz2)
  have t3 : 0 ≤ d.A i 3 * z3 := mul_nonneg h3 (le_of_lt hz3)
  have e2 : d.A i 2 * z2 = 0 := by linarith
  have e3 : d.A i 3 * z3 = 0 := by linarith
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with hj | hj
  · subst hj
    rcases mul_eq_zero.mp e2 with h | h
    · exact h
    · exact absurd h (ne_of_gt hz2)
  · subst hj
    rcases mul_eq_zero.mp e3 with h | h
    · exact h
    · exact absurd h (ne_of_gt hz3)

/-- **The reduction with `A|_{S,Z} = 0` supplied by the kernel direction.**  This is the form
that applies to the configuration left open by `lem:rank2zsign` of the unified note. -/
theorem four_stage_block_impossible_of_pos_kernel
    (hb2 : d.b 2 = 0) (hb3 : d.b 3 = 0)
    (z2 z3 : ℝ) (hz2 : 0 < z2) (hz3 : 0 < z3)
    (hAz : ∀ i ∈ range 2, d.A i 2 * z2 + d.A i 3 * z3 = 0)
    (hKe : ∀ i ∈ range 2, Km4 d i 2 + Km4 d i 3 = 0)
    (hKA : ∀ i ∈ range 2, ∀ j ∈ range 2,
      Km4 d i 2 * d.A 2 j + Km4 d i 3 * d.A 3 j = 0) :
    False :=
  four_stage_block_impossible d hb2 hb3
    (AZ_eq_zero_of_pos_kernel d z2 z3 hz2 hz3 hAz) hKe hKA

end SSP.FourStage
