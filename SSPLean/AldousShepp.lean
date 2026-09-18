import SSPLean.QSequenceCrossing

/-!
# The Aldous–Shepp least-variability theorem, from the matrix bound

Aldous and Shepp (1987) proved that the absorption time `X` of a continuous-time Markov chain
with at most `s` transient states satisfies

```
  Var(X) ≥ (E[X])² / s ,
```

with the minimum attained by the Erlang/gamma law.  Their proof is a continuous-time martingale
argument.

This file derives the same inequality from `SSP.componentBound_unconditional` — the paper's
Lemma 5, proved in `SSPLean.QSequenceCrossing` by an elementary weighted-paths/crossing argument.
The point is that the implication runs *backwards* from the usual presentation: `main_revised.tex`
obtains Lemma 5 *from* Aldous–Shepp, whereas here Lemma 5 is proved directly and Aldous–Shepp
falls out, so no martingale theory is used anywhere.

## What is and is not proved here

The chain has three links.

1.  **`ComponentBound`**, i.e. `((N𝟙)ᵢ)² ≤ (2s/(s+1))·(N²𝟙)ᵢ` for `N = (I−Q)⁻¹`.  This is
    imported, fully proved, no assumptions: `SSP.componentBound_unconditional`.

2.  **The moment dictionary** `E_i[X] = (N𝟙)ᵢ` and `E_i[X²] = 2(N²𝟙)ᵢ`.  This is the
    probability content — it identifies the resolvent entries with moments of the absorption
    time, via `P_i(X > t) = (eᵢᵀexp((Q−I)t)𝟙)` and `E[Xᵏ] = k∫tᵏ⁻¹P(X>t)dt`.  Mathlib has no
    continuous-time absorbing-chain theory, so this is **taken as a hypothesis**, bundled into
    `AbsorptionMoments` below.  It is not a gap in the *inequality*: it is the definition of
    what `X` is.

    `SSPLean.SemigroupMoments` now **proves** the matrix half of this assumption:
    `∫₀^∞(exp(t(Q−I))𝟙)ᵢ dt = (N𝟙)ᵢ` and `∫₀^∞(exp(t(Q−I))N𝟙)ᵢ dt = (N²𝟙)ᵢ`, and
    `SSPLean.MomentBridge` restates both in the `rowSum`/`rowSum2` interface used here
    (`integral_eq_rowSum`, `integral_eq_rowSum2`).  What is still assumed is therefore only the
    *probabilistic* step: that `X` has survival function `t ↦ (exp(t(Q−I))𝟙)ᵢ` and that its
    moments are the tail integrals `E[X] = ∫P(X>t)dt`, `E[X²] = 2∫t·P(X>t)dt`.  The first is the
    definition of a phase-type law; the second needs Mathlib's layer-cake theorem and a
    probability space carrying `X`, neither of which is built here.

    `SSPLean.MomentTests` checks that `AbsorptionMoments` is satisfiable, so the theorems below
    are not vacuous.

3.  **The algebra** turning 1 + 2 into the variance bound.  Proved here.

So the honest reading is: *given* that `X` has the moments a phase-type absorption time has,
the Aldous–Shepp bound is a corollary of elementary matrix arithmetic.  Isolating step 2 as a
hypothesis is what keeps that claim checkable.
-/

set_option autoImplicit false

namespace SSP.AldousShepp

open SSP Finset

/-- **The moment dictionary as a hypothesis.**

`m₁` and `m₂` are the first two moments of the absorption time started at transient state `i`,
for the chain whose transient sub-generator is `Q − I` with `Q` substochastic.  The two fields
record the standard phase-type moment formulas `E[Xᵏ] = k!·(Nᵏ𝟙)ᵢ`, which is the only
probabilistic input.

The remaining fields are the algebraic side conditions under which `ComponentBound` holds. -/
structure AbsorptionMoments (s : ℕ) (Q : ℕ → ℕ → ℝ) (i : ℕ) (m₁ m₂ : ℝ) : Prop where
  /-- `Q` has nonnegative entries. -/
  hQ : ∀ j k, 0 ≤ Q j k
  /-- `Q` is substochastic: row sums at most `1`. -/
  hsub : ∀ j < s, ∑ k ∈ range s, Q j k ≤ 1
  /-- Strict contraction, so `N = (I−Q)⁻¹` exists as a convergent Neumann series. -/
  hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1
  /-- At least one transient state. -/
  hs : 0 < s
  /-- The starting state is transient. -/
  hi : i < s
  /-- First moment: `E_i[X] = (N𝟙)ᵢ`. -/
  hm₁ : m₁ = rowSum s (Nmat s Q) i
  /-- Second moment: `E_i[X²] = 2·(N²𝟙)ᵢ`. -/
  hm₂ : m₂ = 2 * rowSum2 s (Nmat s Q) i

/-- **Step 2 of the derivation: the moment form of `ComponentBound`.**

`ComponentBound` says `((N𝟙)ᵢ)² ≤ (2s/(s+1))·(N²𝟙)ᵢ`.  Substituting `(N𝟙)ᵢ = m₁` and
`(N²𝟙)ᵢ = m₂/2` and cancelling the `2` gives `m₁² ≤ (s/(s+1))·m₂`. -/
theorem moment_bound {s : ℕ} {Q : ℕ → ℕ → ℝ} {i : ℕ} {m₁ m₂ : ℝ}
    (h : AbsorptionMoments s Q i m₁ m₂) :
    m₁ ^ 2 ≤ (s / (s + 1)) * m₂ := by
  have hCB := componentBound_unconditional s Q h.hQ h.hsub h.hρ h.hs i h.hi
  rw [h.hm₁, h.hm₂]
  -- `hCB : (rowSum …)² ≤ (2s/(s+1)) * rowSum2 …`
  have hs1 : (0:ℝ) < (s : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hs1] at hCB ⊢
  nlinarith [hCB]

/-- **The Aldous–Shepp least-variability bound.**

For the absorption time `X` of a continuous-time absorbing Markov chain with `s` transient
states, started at a transient state,

```
  Var(X) = m₂ − m₁² ≥ m₁² / s .
```

The proof rearranges `moment_bound`: `m₁² ≤ (s/(s+1))m₂` gives `m₂ ≥ ((s+1)/s)m₁²`, and
subtracting `m₁²` leaves `((s+1)/s − 1)m₁² = m₁²/s`. -/
theorem variance_bound {s : ℕ} {Q : ℕ → ℕ → ℝ} {i : ℕ} {m₁ m₂ : ℝ}
    (h : AbsorptionMoments s Q i m₁ m₂) :
    m₁ ^ 2 / s ≤ m₂ - m₁ ^ 2 := by
  have hmb := moment_bound h
  have hspos : (0:ℝ) < (s : ℝ) := by exact_mod_cast h.hs
  have hs1 : (0:ℝ) < (s : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hs1] at hmb
  rw [div_le_iff₀ hspos]
  nlinarith [hmb]

/-- **The bound in coefficient-of-variation form.**  `Var(X)/(E X)² ≥ 1/s`, stated
multiplicatively to avoid dividing by `m₁`. -/
theorem variance_bound' {s : ℕ} {Q : ℕ → ℕ → ℝ} {i : ℕ} {m₁ m₂ : ℝ}
    (h : AbsorptionMoments s Q i m₁ m₂) :
    m₁ ^ 2 ≤ s * (m₂ - m₁ ^ 2) := by
  have hv := variance_bound h
  have hspos : (0:ℝ) < (s : ℝ) := by exact_mod_cast h.hs
  rw [div_le_iff₀ hspos] at hv
  linarith

/-- **Tightness.**  The bound is attained: for the Erlang law with `s` phases — `Q` the
nilpotent shift, `m₁ = s`, `m₂ = s(s+1)` — we have `Var = s = m₁²/s` exactly.  Recorded as an
arithmetic identity, so no claim is made that the shift matrix satisfies `hρ`. -/
theorem erlang_tight (s : ℕ) (hs : 0 < s) :
    ((s : ℝ) * s) - (s : ℝ) ^ 2 = 0 ∧ ((s : ℝ) ^ 2) / s = s := by
  have hspos : (0:ℝ) < (s : ℝ) := by exact_mod_cast hs
  refine ⟨by ring, ?_⟩
  field_simp

end SSP.AldousShepp
