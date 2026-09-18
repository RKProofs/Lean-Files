import SSPLean.CanonicalS3
import SSPLean.K2S4Renewal

/-!
# The `k = 2` phase-type moment inequality in every order

This file formalizes the parameter-uniform algebra in `k2_complete_all_s.tex`, including the
strict and equality parts of the renewal lemma, the all-orders strong induction once a
state-return certificate is supplied, and the common-scale equality argument for the final
mixture.  The order-two algebra and the order-three canonical algebra are imported from the
existing development.

Two representation interfaces are deliberately visible rather than postulated as axioms:

* the paper's cited He--Zhang canonical-representation theorem at order three;
* construction of `RenewalCertificate` from a finite CTMC by the strong Markov property.

`SSPLean.CanonicalS3` checks everything after the first representation is supplied, while
`all_stages_of_renewal` checks the complete induction after the second is supplied.  Connecting
the repository's concrete absorption-time measure to `RenewalCertificate` still requires a
formal third-moment dictionary and the state-return decomposition.

The target for raw moments is

`(s + 1) m₁ m₃ ≥ (s + 2) m₂²`.

The present first section records the sharp Erlang moments, mixture closure, and the uniform
corner polynomial occurring in the state-return renewal step.
-/

set_option autoImplicit false

namespace SSP.K2AllStages

open Finset

variable {ι : Type*}

/-! ## Moment-level statement and the sharp family -/

/-- The raw-moment `k = 2` gap at order `s`. -/
noncomputable def gap (s m₁ m₂ m₃ : ℝ) : ℝ :=
  (s + 1) * m₁ * m₃ - (s + 2) * m₂ ^ 2

/-- Raw moments of an atom-at-zero mixture of an `s`-stage Erlang law of stage mean `θ`. -/
noncomputable def erlangMixMoment (s : ℕ) (w θ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => w * s * θ
  | 2 => w * s * (s + 1) * θ ^ 2
  | 3 => w * s * (s + 1) * (s + 2) * θ ^ 3
  | _ => 0

/-- The conjectured extremal family is indeed sharp. -/
theorem erlang_mixture_sharp (s : ℕ) (w θ : ℝ) :
    gap s (erlangMixMoment s w θ 1) (erlangMixMoment s w θ 2)
      (erlangMixMoment s w θ 3) = 0 := by
  simp [gap, erlangMixMoment]
  ring

/-- Mixture closure in raw-moment form. -/
theorem mixture_closure (t : Finset ι) (w m₁ m₂ m₃ : ι → ℝ) (s : ℝ)
    (hs : 0 ≤ s) (hw : ∀ i ∈ t, 0 ≤ w i)
    (h1 : ∀ i ∈ t, 0 ≤ m₁ i) (h2 : ∀ i ∈ t, 0 ≤ m₂ i)
    (h3 : ∀ i ∈ t, 0 ≤ m₃ i)
    (hi : ∀ i ∈ t, (s + 2) * (m₂ i)^2 ≤ (s + 1) * (m₁ i * m₃ i)) :
    (s + 2) * (∑ i ∈ t, w i * m₂ i)^2
      ≤ (s + 1) * ((∑ i ∈ t, w i * m₁ i) * (∑ i ∈ t, w i * m₃ i)) := by
  have hk : 0 ≤ (s + 2) / (s + 1) := by positivity
  have hs1 : 0 < s + 1 := by linarith
  have hcomp : ∀ i ∈ t, ((s + 2) / (s + 1)) * (m₂ i)^2 ≤ m₁ i * m₃ i := by
    intro i hi_mem
    rw [div_mul_eq_mul_div, div_le_iff₀ hs1]
    nlinarith [hi i hi_mem]
  have hmix := SSP.Chain.mixture_closure_sq t w m₁ m₂ m₃ ((s + 2) / (s + 1))
    hk hw h1 h3 h2 hcomp
  rw [div_mul_eq_mul_div, div_le_iff₀ hs1] at hmix
  nlinarith

/-! ## The uniform lower-corner polynomial -/

/-- The normalized value of the renewal gap at `A=A₀`, `B=B₀`.

This is the polynomial extension to the closed region `0 ≤ r ≤ b ≤ 1`; writing it explicitly
avoids division by `1-r` on the boundary. -/
noncomputable def Phi (n r b z : ℝ) : ℝ :=
    -2*b^4*n^2 + 5*b^4*n - 2*b^4
    + 2*b^3*n^3 - 6*b^3*n^2*z - 4*b^3*n^2 + 14*b^3*n*z - 4*b^3*z
    + 3*b^2*n^3*z - 6*b^2*n^2*z^2 - 8*b^2*n^2*z
    + 14*b^2*n*z^2 - 3*b^2*n*z + b^2*n - 2*b^2*z^2
    + b*n^3*z^2 + b*n^3*z - 2*b*n^2*z^3 - 4*b*n^2*z^2
    + 2*b*n^2*z + 6*b*n*z^3 - 3*b*n*z^2 + b*n*z + n*z^4
    + r^2 * (-b^2*n^3 - 2*b^2*n^2 + 2*b*n^3 + 4*b*n^2 - n^3 - 2*n^2)
    + r * (3*b^3*n^3 - 2*b^3*n^2 + b^3*n + 4*b^2*n^3*z - 4*b^2*n^3
      - 6*b^2*n^2*z - 2*b^2*n*z + b*n^3*z^2 - 3*b*n^3*z + b*n^3
      - 4*b*n^2*z^2 + 8*b*n^2*z + 2*b*n^2 - 3*b*n*z^2
      + 3*b*n*z - b*n - n^3*z^2 - n^3*z + 4*n^2*z^2 - 2*n^2*z
      + 3*n*z^2 - n*z)

noncomputable def Acoef (n y : ℝ) : ℝ :=
  n*y^4 + (-2*n^2+6*n)*y^3 + (-6*n^2+14*n-2)*y^2
    + (-6*n^2+14*n-4)*y - 2*n^2+5*n-2

noncomputable def Bcoef (n y : ℝ) : ℝ :=
  n*(n^2-4*n-3)*y^2 + n*(3*n^2-8*n-3)*y + 2*n^2*(n-2)

noncomputable def Ccoef (n y : ℝ) : ℝ := n + n*(n+1)^2*y

/-- Chord form of concavity of `Phi` in `r`. -/
theorem phi_chord (n r b z : ℝ) :
    b * Phi n r b z = (b-r) * Phi n 0 b z + r * Phi n b b z
      + n^2*(n+2)*b*(1-b)^2*r*(b-r) := by
  unfold Phi
  ring

theorem phi_at_b (n b z : ℝ) :
    Phi n b b z = (2*(n-1)*b^2 + 4*n*b*z + n*z^2) * (z-(n-1)*b)^2 := by
  unfold Phi
  ring

theorem phi_at_zero_scaled (n b y : ℝ) :
    Phi n 0 b (b*y) = b^2 * (Acoef n y*b^2 + Bcoef n y*b + Ccoef n y) := by
  unfold Phi Acoef Bcoef Ccoef
  ring

theorem endpoint_one_factor (n y : ℝ) :
    Acoef n y + Bcoef n y + Ccoef n y
      = (n*y^2 + 4*n*y + 2*(n-1)) * (y-(n-1))^2 := by
  unfold Acoef Bcoef Ccoef
  ring

/-- The exceptional `n=4` discriminant identity. -/
theorem corner_discriminant_four (y : ℝ) :
    (Bcoef 4 y / 2)^2 - 4*(Acoef 4 y / 2)*(Ccoef 4 y / 2)
      = -20*(y+1)^2*(20*y^3 - 81*y^2 - 54*y - 54) := by
  unfold Acoef Bcoef Ccoef
  ring

theorem bcoef_pos_of_five (n y : ℝ) (hn : 5 ≤ n) (hy : 0 ≤ y) :
    0 < Bcoef n y := by
  have hn0 : 0 < n := by linarith
  have hq2 : 0 < n^2 - 4*n - 3 := by
    have hid : n^2 - 4*n - 3 = (n-5)*(n+1)+2 := by ring
    rw [hid]
    positivity
  have hq1 : 0 < 3*n^2 - 8*n - 3 := by
    have hid : 3*n^2 - 8*n - 3 = (n-5)*(3*n+7)+32 := by ring
    rw [hid]
    positivity
  unfold Bcoef
  have hn2 : 0 < n-2 := by linarith
  have h0 : 0 < 2*n^2*(n-2) := mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hn0)) hn2
  have h1 : 0 ≤ n*(3*n^2-8*n-3)*y := by positivity
  have h2 : 0 ≤ n*(n^2-4*n-3)*y^2 := by positivity
  linarith

theorem ccoef_pos (n y : ℝ) (hn : 0 < n) (hy : 0 ≤ y) :
    0 < Ccoef n y := by
  unfold Ccoef
  positivity

theorem endpoint_sum_nonneg (n y : ℝ) (hn : 1 ≤ n) (hy : 0 ≤ y) :
    0 ≤ Acoef n y + Bcoef n y + Ccoef n y := by
  rw [endpoint_one_factor]
  have hfac : 0 ≤ n*y^2 + 4*n*y + 2*(n-1) := by positivity
  positivity

/-- Positivity of the `r=0` quadratic for the uniform range `n ≥ 5`. -/
theorem corner_quadratic_nonneg_of_five (n y b : ℝ)
    (hn : 5 ≤ n) (hy : 0 ≤ y) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ Acoef n y*b^2 + Bcoef n y*b + Ccoef n y := by
  have hB : 0 < Bcoef n y := bcoef_pos_of_five n y hn hy
  have hC : 0 < Ccoef n y := ccoef_pos n y (by linarith) hy
  have hsum : 0 ≤ Acoef n y + Bcoef n y + Ccoef n y :=
    endpoint_sum_nonneg n y (by linarith) hy
  rcases le_or_gt (Acoef n y) 0 with hA | hA
  · have hid : Acoef n y*b^2 + Bcoef n y*b + Ccoef n y
        = (1-b)*Ccoef n y + b*(Acoef n y+Bcoef n y+Ccoef n y)
          + (-Acoef n y)*b*(1-b) := by ring
    rw [hid]
    have h₁ : 0 ≤ (1-b)*Ccoef n y := mul_nonneg (by linarith) (le_of_lt hC)
    have h₂ : 0 ≤ b*(Acoef n y+Bcoef n y+Ccoef n y) := mul_nonneg hb0 hsum
    have h₃ : 0 ≤ (-Acoef n y)*b*(1-b) :=
      mul_nonneg (mul_nonneg (neg_nonneg.mpr hA) hb0) (by linarith)
    linarith
  · have hAb : 0 ≤ Acoef n y*b^2 := by positivity
    have hBb : 0 ≤ Bcoef n y*b := by positivity
    linarith

theorem bcoef_four_factor (y : ℝ) :
    Bcoef 4 y / 2 = -2*(3*y-16)*(y+1) := by
  unfold Bcoef
  ring

theorem cubic_four_pos (y : ℝ) (hy : 16/3 < y) :
    0 < 20*y^3 - 81*y^2 - 54*y - 54 := by
  let t := y - 16/3
  have ht : 0 < t := by dsimp [t]; linarith
  have hid : 20*y^3 - 81*y^2 - 54*y - 54
      = 20*t^3 + 239*t^2 + (2366/3)*t + 10478/27 := by
    dsimp [t]
    ring
  rw [hid]
  positivity

/-- Positivity of the exceptional `n=4` corner quadratic. -/
theorem corner_quadratic_nonneg_four (y b : ℝ)
    (hy : 0 ≤ y) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ Acoef 4 y*b^2 + Bcoef 4 y*b + Ccoef 4 y := by
  let A := Acoef 4 y / 2
  let B := Bcoef 4 y / 2
  let C := Ccoef 4 y / 2
  have hC : 0 < C := by
    dsimp [C, Ccoef]
    positivity
  have hsum : 0 ≤ A+B+C := by
    dsimp [A, B, C]
    have h := endpoint_sum_nonneg 4 y (by norm_num) hy
    linarith
  have hscale : Acoef 4 y*b^2 + Bcoef 4 y*b + Ccoef 4 y
      = 2*(A*b^2+B*b+C) := by
    dsimp [A, B, C]
    ring
  rw [hscale]
  apply mul_nonneg (by norm_num)
  rcases le_or_gt A 0 with hA | hA
  · have hid : A*b^2+B*b+C = (1-b)*C + b*(A+B+C) + (-A)*b*(1-b) := by ring
    rw [hid]
    have h₁ : 0 ≤ (1-b)*C := mul_nonneg (by linarith) (le_of_lt hC)
    have h₂ : 0 ≤ b*(A+B+C) := mul_nonneg hb0 hsum
    have h₃ : 0 ≤ (-A)*b*(1-b) :=
      mul_nonneg (mul_nonneg (neg_nonneg.mpr hA) hb0) (by linarith)
    linarith
  · rcases le_or_gt 0 B with hB | hB
    · have hAb : 0 ≤ A*b^2 := by positivity
      have hBb : 0 ≤ B*b := by positivity
      linarith
    · have hy16 : 16/3 < y := by
        have hfac := bcoef_four_factor y
        dsimp [B] at hB
        rw [hfac] at hB
        by_contra hnot
        have hupp : y ≤ 16/3 := le_of_not_gt hnot
        have hp : 0 ≤ (16-3*y)*(y+1) := mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hcub := cubic_four_pos y hy16
      have hdisc : B^2 - 4*A*C < 0 := by
        have hd := corner_discriminant_four y
        dsimp [A, B, C]
        rw [hd]
        have : 0 < (y+1)^2 := by positivity
        nlinarith [mul_pos this hcub]
      have hsquare : 0 ≤ (2*A*b+B)^2 := sq_nonneg _
      have hid : 4*A*(A*b^2+B*b+C) = (2*A*b+B)^2 + (4*A*C-B^2) := by ring
      have hprod : 0 < 4*A*(A*b^2+B*b+C) := by nlinarith
      nlinarith

/-- The normalized lower corner is nonnegative for every integer `n ≥ 4`. -/
theorem corner_nonneg (n : ℕ) (hn : 4 ≤ n) (r b z : ℝ)
    (hr0 : 0 ≤ r) (hrb : r ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ Phi n r b z := by
  have hb0 : 0 ≤ b := le_trans hr0 hrb
  rcases eq_or_lt_of_le hb0 with hb | hb
  · subst b
    have hr : r = 0 := by linarith
    subst r
    unfold Phi
    have hn0 : (0:ℝ) ≤ n := by positivity
    norm_num
    have hz4 : z^4 = (z^2)^2 := by ring
    rw [hz4]
    exact mul_nonneg hn0 (sq_nonneg _)
  · let y := z / b
    have hy : 0 ≤ y := div_nonneg hz (le_of_lt hb)
    have hzy : z = b*y := by
      dsimp [y]
      field_simp
    have hq : 0 ≤ Acoef n y*b^2 + Bcoef n y*b + Ccoef n y := by
      by_cases h4 : n = 4
      · subst n
        exact corner_quadratic_nonneg_four y b hy (le_of_lt hb) hb1
      · have h5n : 5 ≤ n := by omega
        have h5r : (5:ℝ) ≤ (n:ℝ) := by exact_mod_cast h5n
        exact corner_quadratic_nonneg_of_five n y b h5r hy (le_of_lt hb) hb1
    have hzero : 0 ≤ Phi n 0 b z := by
      rw [hzy, phi_at_zero_scaled]
      positivity
    have hn4 : (4:ℝ) ≤ n := by exact_mod_cast hn
    have hbval : 0 ≤ Phi n b b z := by
      rw [phi_at_b]
      have hn1 : 0 ≤ (n:ℝ)-1 := by linarith
      have hfac : 0 ≤ 2*((n:ℝ)-1)*b^2 + 4*n*b*z + n*z^2 := by positivity
      positivity
    have hcorr : 0 ≤ (n:ℝ)^2*(n+2)*b*(1-b)^2*r*(b-r) := by positivity
    have hch := phi_chord (n:ℝ) r b z
    have hbpos : 0 < b := hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hrb) hzero, mul_nonneg hr0 hbval]

/-- Strict corner positivity in the genuine interior routing region. -/
theorem corner_pos_interior (n : ℕ) (hn : 4 ≤ n) (r b z : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 ≤ z) :
    0 < Phi n r b z := by
  let nr : ℝ := n
  have hzero : 0 ≤ Phi nr 0 b z :=
    corner_nonneg n hn 0 b z (by norm_num) (by linarith) (le_of_lt hb1) hz
  have hbval : 0 ≤ Phi nr b b z :=
    corner_nonneg n hn b b z (by linarith) le_rfl (le_of_lt hb1) hz
  have hch := phi_chord nr r b z
  have hcorr : 0 < nr^2*(nr+2)*b*(1-b)^2*r*(b-r) := by
    have hnr : 0 < nr := by dsimp [nr]; positivity
    have hb0 : 0 < b := lt_trans hr0 hrb
    positivity
  have hleft : 0 ≤ (b-r)*Phi nr 0 b z := mul_nonneg (by linarith) hzero
  have hright : 0 ≤ r*Phi nr b b z := mul_nonneg (le_of_lt hr0) hbval
  have : 0 < b*Phi nr r b z := by nlinarith
  exact pos_of_mul_pos_right this (by linarith)

/-! ## The two boundary and interior certificates -/

noncomputable def SBeta (n r b z : ℝ) : ℝ :=
  -2*n*(n+2)*r*b + (n^2+5)*b^2 + (n^2+7)*b*z + 2*z^2
    + 2*n*(n+2)*r - 2*n*(n+2)*b

noncomputable def MBeta (n b z : ℝ) : ℝ := (n+1)^2*b+z

noncomputable def KBeta (n r b z : ℝ) : ℝ :=
  4*MBeta n b z*Phi n r b z - n*z*(SBeta n r b z)^2

noncomputable def TBeta (n b z : ℝ) : ℝ :=
  (8*n^3-12*n^2-12*n+8)*b^2
    + (n^4+7*n^3+3*n^2-19*n+8)*b*z
    + (-8*n^4+8*n^3+16*n^2)*b + (-12*n^2+12*n)*z - 4*n^2-4*n

/-- Chord form of concavity of the `A=A₀` stationary-value certificate. -/
theorem kBeta_chord (n r t b z : ℝ) :
    t * KBeta n r b z = (t-r)*KBeta n 0 b z + r*KBeta n t b z
      + 4*n^2*(n+1)^2*(n+2)*(b+z)*(1-b)^2*t*r*(t-r) := by
  unfold KBeta MBeta SBeta Phi
  ring

theorem kBeta_at_zero (n b z : ℝ) :
    KBeta n 0 b z = -(n+1)*b*(b+z)^2*TBeta n b z := by
  unfold KBeta MBeta SBeta TBeta Phi
  ring

theorem kBeta_at_b (n b z : ℝ) :
    KBeta n b b z = (n^2-1)^2*(8*(n-1)*b-(n+8)*z)*b^2*(b+z)^2 := by
  unfold KBeta MBeta SBeta Phi
  ring

noncomputable def DBeta (n y : ℝ) : ℝ := n^2+5+(n^2+7)*y+2*y^2

noncomputable def PBeta (n y : ℝ) : ℝ :=
  4*(n+1)*y^3 + (12*n^3+4*n^2-8*n+24)*y^2
    + (3*n^5-13*n^4+4*n^3+16*n^2-55*n+45)*y
    + 4*n^5-12*n^4+5*n^3+35*n^2-57*n+25

theorem sBeta_at_zero_scaled (n b y : ℝ) :
    SBeta n 0 b (b*y) = b * (b*DBeta n y - 2*n*(n+2)) := by
  unfold SBeta DBeta
  ring

theorem sBeta_at_b_scaled (n b y : ℝ) :
    SBeta n b b (b*y)
      = b^2 * (2*y^2+(n^2+7)*y-(n-1)*(n+5)) := by
  unfold SBeta
  ring

theorem tBeta_scaled (n b y : ℝ) :
    TBeta n b (b*y)
      = b^2*((8*n^3-12*n^2-12*n+8)
          +(n^4+7*n^3+3*n^2-19*n+8)*y)
        + b*((-8*n^4+8*n^3+16*n^2)+(-12*n^2+12*n)*y)
        - 4*n*(n+1) := by
  unfold TBeta
  ring

theorem tBeta_one_scaled (n y : ℝ) :
    TBeta n 1 y = (n-1)^2*(n+1)*((n+8)*y-8*(n-1)) := by
  unfold TBeta
  ring

theorem tBeta_moving_identity (n y : ℝ) :
    let den := DBeta n y
    let cap := 2*n*(n+2)
    let a := 8*n^3-12*n^2-12*n+8+(n^4+7*n^3+3*n^2-19*n+8)*y
    let c := -8*n^4+8*n^3+16*n^2+(-12*n^2+12*n)*y
    a*cap^2 + c*cap*den + (-4*n^2-4*n)*den^2
      = -4*n*(y+(n+1)^2)*PBeta n y := by
  dsimp
  unfold DBeta PBeta
  ring

noncomputable def FBeta (n y : ℝ) : ℝ :=
  2*y^2+(n^2+7)*y-(n-1)*(n+5)

theorem dBeta_sub_cap (n y : ℝ) :
    DBeta n y - 2*n*(n+2) = FBeta n y := by
  unfold DBeta FBeta
  ring

theorem fBeta_threshold_identity (n y : ℝ) :
    (n+8)^2*FBeta n y
      = n*(7*n^3+36*n^2-3*n-40)
        + ((n+8)*y-8*(n-1))*(n^3+8*n^2+2*n*y+23*n+16*y+40) := by
  unfold FBeta
  ring

theorem fBeta_threshold (n y : ℝ) (hn : 4 ≤ n) (hy : 0 ≤ y)
    (hf : FBeta n y ≤ 0) :
    (n+8)*y ≤ 8*(n-1) := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hbase : 0 < 7*n^3+36*n^2-3*n-40 := by
    have hid : 7*n^3+36*n^2-3*n-40
        = 7*m^3+120*m^2+621*m+972 := by dsimp [m]; ring
    rw [hid]
    positivity
  have hn0 : 0 < n := by linarith
  have hcoef : 0 < n^3+8*n^2+2*n*y+23*n+16*y+40 := by positivity
  have hid := fBeta_threshold_identity n y
  by_contra h
  have hgap : 0 < (n+8)*y-8*(n-1) := by linarith
  have hrhs : 0 < n*(7*n^3+36*n^2-3*n-40)
      + ((n+8)*y-8*(n-1))*(n^3+8*n^2+2*n*y+23*n+16*y+40) := by positivity
  have hlhs : (n+8)^2*FBeta n y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hf
  linarith

theorem fBeta_threshold_strict (n y : ℝ) (hn : 4 ≤ n) (hy : 0 ≤ y)
    (hf : FBeta n y < 0) :
    (n+8)*y < 8*(n-1) := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hbase : 0 < 7*n^3+36*n^2-3*n-40 := by
    have hid : 7*n^3+36*n^2-3*n-40
        = 7*m^3+120*m^2+621*m+972 := by dsimp [m]; ring
    rw [hid]
    positivity
  have hn0 : 0 < n := by linarith
  have hcoef : 0 < n^3+8*n^2+2*n*y+23*n+16*y+40 := by positivity
  have hid := fBeta_threshold_identity n y
  by_contra h
  have hgap : 0 ≤ (n+8)*y-8*(n-1) := by linarith
  have hrhs : 0 < n*(7*n^3+36*n^2-3*n-40)
      +((n+8)*y-8*(n-1))*(n^3+8*n^2+2*n*y+23*n+16*y+40) := by
    have hfirst : 0 < n*(7*n^3+36*n^2-3*n-40) := mul_pos hn0 hbase
    have hsecond : 0 ≤ ((n+8)*y-8*(n-1))
        *(n^3+8*n^2+2*n*y+23*n+16*y+40) := mul_nonneg hgap (le_of_lt hcoef)
    linarith
  have hlhs : (n+8)^2*FBeta n y < 0 := mul_neg_of_pos_of_neg (sq_pos_of_pos (by linarith)) hf
  linarith

noncomputable def PBetaShift (m y : ℝ) : ℝ :=
  (4*m+20)*y^3 + (12*m^3+148*m^2+600*m+824)*y^2
    + (3*m^5+47*m^4+276*m^3+736*m^2+777*m+81)*y
    + 4*m^5+68*m^4+453*m^3+1503*m^2+2511*m+1701

theorem pBeta_shift (m y : ℝ) : PBeta (m+4) y = PBetaShift m y := by
  unfold PBeta PBetaShift
  ring

theorem pBeta_pos (n y : ℝ) (hn : 4 ≤ n) (hy : 0 ≤ y) : 0 < PBeta n y := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hnrep : n = m+4 := by dsimp [m]; ring
  rw [hnrep, pBeta_shift]
  unfold PBetaShift
  positivity

theorem dBeta_pos (n y : ℝ) (hn : 4 ≤ n) (hy : 0 ≤ y) : 0 < DBeta n y := by
  unfold DBeta
  positivity

theorem tBeta_chord_scaled (n y b t : ℝ) :
    let a := 8*n^3-12*n^2-12*n+8+(n^4+7*n^3+3*n^2-19*n+8)*y
    t*TBeta n b (b*y) = (t-b)*TBeta n 0 0 + b*TBeta n t (t*y) - a*b*t*(t-b) := by
  dsimp
  unfold TBeta
  ring_nf

theorem tBeta_moving_value (n y : ℝ) (hden : DBeta n y ≠ 0) :
    (DBeta n y)^2 * TBeta n (2*n*(n+2)/DBeta n y)
        ((2*n*(n+2)/DBeta n y)*y)
      = -4*n*(y+(n+1)^2)*PBeta n y := by
  rw [← tBeta_moving_identity]
  unfold TBeta
  field_simp [hden]
  ring

theorem tBeta_le_zero (n : ℕ) (hn : 4 ≤ n) (y b : ℝ)
    (hy : 0 ≤ y) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hfeas : b*DBeta n y ≤ 2*n*(n+2)) :
    TBeta n b (b*y) ≤ 0 := by
  let nr : ℝ := n
  let den := DBeta nr y
  let cap := 2*nr*(nr+2)
  let a := 8*nr^3-12*nr^2-12*nr+8+(nr^4+7*nr^3+3*nr^2-19*nr+8)*y
  change TBeta nr b (b*y) ≤ 0
  have hnr : 4 ≤ nr := by dsimp [nr]; exact_mod_cast hn
  have hden : 0 < den := dBeta_pos nr y hnr hy
  have hcap : 0 < cap := by dsimp [cap, nr]; positivity
  have ha : 0 < a := by
    let m := nr-4
    have hm : 0 ≤ m := by dsimp [m]; linarith
    have hid : a = 8*m^3+84*m^2+276*m+280
        +(m^4+23*m^3+183*m^2+597*m+684)*y := by
      dsimp [a, m]
      ring
    rw [hid]
    positivity
  have hT0 : TBeta nr 0 0 < 0 := by
    unfold TBeta
    have hn0 : 0 < nr := by linarith
    nlinarith [mul_pos hn0 (show 0 < nr+1 by linarith)]
  rcases le_total den cap with hdc | hcd
  · have hf : FBeta nr y ≤ 0 := by
      rw [← dBeta_sub_cap]
      exact sub_nonpos.mpr hdc
    have hthreshold := fBeta_threshold nr y hnr hy hf
    have hT1 : TBeta nr 1 y ≤ 0 := by
      rw [tBeta_one_scaled]
      have hpre : 0 ≤ (nr-1)^2*(nr+1) := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos hpre (by linarith)
    have hch := tBeta_chord_scaled nr y b 1
    norm_num at hch
    have h₁ : (1-b)*TBeta nr 0 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hT0)
    have h₂ : b*TBeta nr 1 y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 hT1
    have h₃ : 0 ≤ a*b*1*(1-b) := by positivity
    dsimp [a] at h₃
    nlinarith
  · let t := cap/den
    have ht : 0 < t := div_pos hcap hden
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_one hden).mpr hcd
    have hbt : b ≤ t := by
      dsimp [t, cap, den, nr] at *
      exact (le_div_iff₀ hden).mpr hfeas
    have hPt : 0 < PBeta nr y := pBeta_pos nr y hnr hy
    have hTt : TBeta nr t (t*y) < 0 := by
      have hid := tBeta_moving_value nr y (ne_of_gt hden)
      dsimp [t, cap, den] at *
      have hn0 : 0 < nr := by linarith
      have hysq : 0 < y+(nr+1)^2 := by nlinarith [sq_pos_of_pos (show 0 < nr+1 by linarith)]
      have hrhs : -4*nr*(y+(nr+1)^2)*PBeta nr y < 0 := by
        have : 0 < 4*nr*(y+(nr+1)^2)*PBeta nr y := by positivity
        linarith
      have hden2 : 0 < (DBeta nr y)^2 := sq_pos_of_pos hden
      have hscaled : (DBeta nr y)^2 * TBeta nr (2*nr*(nr+2)/DBeta nr y)
          ((2*nr*(nr+2)/DBeta nr y)*y) < 0 := by
        rw [hid]
        exact hrhs
      nlinarith
    have hch := tBeta_chord_scaled nr y b t
    dsimp at hch
    have h₁ : (t-b)*TBeta nr 0 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hT0)
    have h₂ : b*TBeta nr t (t*y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 (le_of_lt hTt)
    have h₃ : 0 ≤ a*b*t*(t-b) := by positivity
    dsimp [a] at h₃
    have htT : t * TBeta nr b (b*y) ≤ 0 := by nlinarith
    by_contra hnot
    have hpos : 0 < TBeta nr b (b*y) := lt_of_not_ge hnot
    have := mul_pos ht hpos
    linarith

noncomputable def SAlpha (n r b z : ℝ) : ℝ :=
  2*n*(n+2)*r*(1-b) + 2*n*(n-2)*b^2 + (3*n^2-8*n-3)*b*z
    + (n^2-4*n-3)*z^2 + 2*b + 2*(n+1)^2*z

theorem sAlpha_pos_of_five (n r b z : ℝ) (hn : 5 ≤ n)
    (hr : 0 ≤ r) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z)
    (hbnz : 0 < b + z) :
    0 < SAlpha n r b z := by
  have hn0 : 0 < n := by linarith
  have hn2 : 0 < n-2 := by linarith
  have hq1 : 0 < 3*n^2-8*n-3 := by
    have hid : 3*n^2-8*n-3 = (n-5)*(3*n+7)+32 := by ring
    rw [hid]
    positivity
  have hq2 : 0 < n^2-4*n-3 := by
    have hid : n^2-4*n-3 = (n-5)*(n+1)+2 := by ring
    rw [hid]
    positivity
  unfold SAlpha
  have h₁ : 0 ≤ 2*n*(n+2)*r*(1-b) := by positivity
  have h₂ : 0 ≤ 2*n*(n-2)*b^2 := by positivity
  have h₃ : 0 ≤ (3*n^2-8*n-3)*b*z := by positivity
  have h₄ : 0 ≤ (n^2-4*n-3)*z^2 := by positivity
  have h₅ : 0 < 2*b + 2*(n+1)^2*z := by
    nlinarith [sq_nonneg (n+1), mul_nonneg (sq_nonneg (n+1)) hz]
  linarith

noncomputable def InteriorR0 (n x u : ℝ) : ℝ := 2*(n-1)^2*(n+1)*(x+u)^2

noncomputable def InteriorR1 (n x u v : ℝ) : ℝ :=
  2*(n-1)^2*(n+1)*x^2 + (3*n^3+n^2+n+3)*x*u + (n+1)*u^2
    + ((n-1)*(2*n^2+1)/2)*(x*v+u*v)

noncomputable def InteriorR2 (n x u v : ℝ) : ℝ :=
  2*(n-1)^2*(n+1)*x^2 + 2*(n+1)^3*x*u + (n-1)*(2*n^2+1)*x*v
    + 2*(n+1)*u*v + 3*(n-1)*v^2

noncomputable def InteriorR (n x u v p q : ℝ) : ℝ :=
  InteriorR0 n x u*p^2 + 2*InteriorR1 n x u v*p*q + InteriorR2 n x u v*q^2

theorem interiorR_pos (n x u v p q : ℝ) (hn : 4 ≤ n)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) :
    0 < InteriorR n x u v p q := by
  have hn1 : 0 < n-1 := by linarith
  have hnp : 0 < n+1 := by linarith
  have hR0 : 0 < InteriorR0 n x u := by
    unfold InteriorR0
    positivity
  have hR1 : 0 < InteriorR1 n x u v := by
    unfold InteriorR1
    have hc : 0 < 3*n^3+n^2+n+3 := by nlinarith [mul_pos hn1 hnp, sq_nonneg n]
    positivity
  have hR2 : 0 < InteriorR2 n x u v := by
    unfold InteriorR2
    positivity
  unfold InteriorR
  positivity

theorem sBeta_affine (n r t b z : ℝ) :
    SBeta n t b z = SBeta n r b z + 2*n*(n+2)*(1-b)*(t-r) := by
  unfold SBeta
  ring

set_option maxHeartbeats 2000000 in
/-- Nonnegativity of the stationary-value certificate on the feasible part of `A=A₀`. -/
theorem kBeta_nonneg (n : ℕ) (hn : 4 ≤ n) (r b z : ℝ)
    (hr0 : 0 ≤ r) (hrb : r ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z)
    (hS : SBeta n r b z ≤ 0) :
    0 ≤ KBeta n r b z := by
  have hb0 : 0 ≤ b := le_trans hr0 hrb
  by_cases hbzero : b = 0
  · subst b
    have hr : r = 0 := by linarith
    subst r
    have hz0 : z = 0 := by
      unfold SBeta at hS
      nlinarith [sq_nonneg z]
    subst z
    simp [KBeta, MBeta, SBeta, Phi]
  · have hb : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbzero)
    let nr : ℝ := n
    let y := z/b
    have hnr : 4 ≤ nr := by dsimp [nr]; exact_mod_cast hn
    have hy : 0 ≤ y := div_nonneg hz (le_of_lt hb)
    have hzy : z = b*y := by
      dsimp [y]
      field_simp
    have hS0le : SBeta nr 0 b z ≤ 0 := by
      have haff := sBeta_affine nr 0 r b z
      have hslope : 0 ≤ 2*nr*(nr+2)*(1-b)*r := by positivity
      change SBeta nr r b z ≤ 0 at hS
      nlinarith
    have hfeas : b*DBeta nr y ≤ 2*nr*(nr+2) := by
      have hs0 := sBeta_at_zero_scaled nr b y
      rw [← hzy] at hs0
      have hbpos : 0 < b := hb
      nlinarith
    have hT : TBeta nr b z ≤ 0 := by
      rw [hzy]
      exact tBeta_le_zero n hn y b hy (le_of_lt hb) hb1 hfeas
    have hK0 : 0 ≤ KBeta nr 0 b z := by
      rw [kBeta_at_zero]
      have hpre : 0 ≤ (nr+1)*b*(b+z)^2 := by positivity
      have hpT : (nr+1)*b*(b+z)^2*TBeta nr b z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpre hT
      linarith
    rcases le_total (SBeta nr b b z) 0 with hSb | hSb
    · have hf : FBeta nr y ≤ 0 := by
        have hsbb := sBeta_at_b_scaled nr b y
        rw [← hzy] at hsbb
        have hb2 : 0 < b^2 := sq_pos_of_pos hb
        rw [hsbb] at hSb
        change b^2 * FBeta nr y ≤ 0 at hSb
        by_contra hnot
        have : 0 < FBeta nr y := lt_of_not_ge hnot
        have := mul_pos hb2 this
        linarith
      have hthreshold := fBeta_threshold nr y hnr hy hf
      have hKb : 0 ≤ KBeta nr b b z := by
        rw [kBeta_at_b]
        have hfac : 0 ≤ 8*(nr-1)*b-(nr+8)*z := by
          rw [hzy]
          have hbr : 0 ≤ 8*(nr-1)-(nr+8)*y := by linarith
          nlinarith [mul_nonneg (le_of_lt hb) hbr]
        positivity
      have hch := kBeta_chord nr r b b z
      have hcorr : 0 ≤ 4*nr^2*(nr+1)^2*(nr+2)*(b+z)*(1-b)^2*b*r*(b-r) := by
        positivity
      have hleft : 0 ≤ (b-r)*KBeta nr 0 b z := mul_nonneg (sub_nonneg.mpr hrb) hK0
      have hright : 0 ≤ r*KBeta nr b b z := mul_nonneg hr0 hKb
      have hbK : 0 ≤ b*KBeta nr r b z := by nlinarith
      by_contra hnot
      have hneg : KBeta nr r b z < 0 := lt_of_not_ge hnot
      nlinarith [mul_neg_of_pos_of_neg hb hneg]
    · rcases eq_or_lt_of_le hS with hSr | hSr
      · have hphi := corner_nonneg n hn r b z hr0 hrb hb1 hz
        have hM : 0 ≤ MBeta nr b z := by unfold MBeta; positivity
        unfold KBeta
        change SBeta nr r b z = 0 at hSr
        change 0 ≤ Phi nr r b z at hphi
        rw [hSr]
        norm_num
        exact mul_nonneg (mul_nonneg (by norm_num) hM) hphi
      · have hbone : b < 1 := by
          by_contra hnot
          have hbge : 1 ≤ b := le_of_not_gt hnot
          have hbeq : b = 1 := by linarith
          subst b
          have haff := sBeta_affine nr r 1 1 z
          norm_num at haff
          change SBeta nr r 1 z < 0 at hSr
          linarith
        let c := 2*nr*(nr+2)*(1-b)
        have hc : 0 < c := by dsimp [c]; positivity
        let t := r + (-SBeta nr r b z)/c
        have htr : r < t := by
          dsimp [t]
          have : 0 < (-SBeta nr r b z)/c := div_pos (by linarith) hc
          linarith
        have hSt : SBeta nr t b z = 0 := by
          have haff := sBeta_affine nr r t b z
          have hct : c*(t-r) = -SBeta nr r b z := by
            dsimp [t]
            field_simp [ne_of_gt hc]
            ring
          change SBeta nr t b z = SBeta nr r b z + c*(t-r) at haff
          linarith
        have htb : t ≤ b := by
          have haff := sBeta_affine nr t b b z
          rw [hSt] at haff
          have hspos : 0 < 2*nr*(nr+2)*(1-b) := by positivity
          by_contra hnot
          have hbtneg : b-t < 0 := sub_neg.mpr (lt_of_not_ge hnot)
          have hprod : 2*nr*(nr+2)*(1-b)*(b-t) < 0 := mul_neg_of_pos_of_neg hspos hbtneg
          linarith
        have ht0 : 0 < t := lt_of_le_of_lt hr0 htr
        have hphi := corner_nonneg n hn t b z (le_of_lt ht0) htb hb1 hz
        have hM : 0 ≤ MBeta nr b z := by unfold MBeta; positivity
        have hKt : 0 ≤ KBeta nr t b z := by
          unfold KBeta
          change 0 ≤ Phi nr t b z at hphi
          rw [hSt]
          norm_num
          exact mul_nonneg (mul_nonneg (by norm_num) hM) hphi
        have hch := kBeta_chord nr r t b z
        have hcorr : 0 ≤ 4*nr^2*(nr+1)^2*(nr+2)*(b+z)*(1-b)^2*t*r*(t-r) := by
          positivity
        have hleft : 0 ≤ (t-r)*KBeta nr 0 b z := mul_nonneg (by linarith) hK0
        have hright : 0 ≤ r*KBeta nr t b z := mul_nonneg hr0 hKt
        have htK : 0 ≤ t*KBeta nr r b z := by nlinarith
        by_contra hnot
        have hneg : KBeta nr r b z < 0 := lt_of_not_ge hnot
        nlinarith [mul_neg_of_pos_of_neg ht0 hneg]

/-- In the genuine interior of the routing region, the beta-face stationary certificate is
strictly positive whenever a stationary point is feasible. -/
theorem kBeta_pos_interior (n : ℕ) (hn : 4 ≤ n) (r b z : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 < z)
    (hS : SBeta n r b z < 0) :
    0 < KBeta n r b z := by
  let nr : ℝ := n
  have hnr : 4 ≤ nr := by dsimp [nr]; exact_mod_cast hn
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hS0 : SBeta nr 0 b z < 0 := by
    have haff := sBeta_affine nr 0 r b z
    have hslope : 0 < 2*nr*(nr+2)*(1-b)*r := by positivity
    change SBeta nr r b z < 0 at hS
    nlinarith
  have hK0 : 0 ≤ KBeta nr 0 b z :=
    kBeta_nonneg n hn 0 b z (by norm_num) (le_of_lt hb0) (le_of_lt hb1)
      (le_of_lt hz) (le_of_lt hS0)
  rcases le_total (SBeta nr b b z) 0 with hSb | hSb
  · have hKb : 0 ≤ KBeta nr b b z :=
      kBeta_nonneg n hn b b z (le_of_lt hb0) le_rfl (le_of_lt hb1)
        (le_of_lt hz) hSb
    have hch := kBeta_chord nr r b b z
    have hcorr : 0 < 4*nr^2*(nr+1)^2*(nr+2)*(b+z)*(1-b)^2*b*r*(b-r) := by
      positivity
    have hleft : 0 ≤ (b-r)*KBeta nr 0 b z := mul_nonneg (by linarith) hK0
    have hright : 0 ≤ r*KBeta nr b b z := mul_nonneg (le_of_lt hr0) hKb
    have hbK : 0 < b*KBeta nr r b z := by nlinarith
    exact pos_of_mul_pos_right hbK (le_of_lt hb0)
  · let c := 2*nr*(nr+2)*(1-b)
    have hc : 0 < c := by dsimp [c]; positivity
    let t := r+(-SBeta nr r b z)/c
    have htr : r < t := by
      dsimp [t]
      have hneg : 0 < -SBeta nr r b z := neg_pos.mpr hS
      have hdiv : 0 < (-SBeta nr r b z)/c := div_pos hneg hc
      linarith
    have hSt : SBeta nr t b z = 0 := by
      have haff := sBeta_affine nr r t b z
      have hct : c*(t-r) = -SBeta nr r b z := by
        dsimp [t]
        field_simp [ne_of_gt hc]
        ring
      change SBeta nr t b z = SBeta nr r b z+c*(t-r) at haff
      linarith
    have htb : t ≤ b := by
      have haff := sBeta_affine nr t b b z
      rw [hSt] at haff
      have hslope : 0 < 2*nr*(nr+2)*(1-b) := by positivity
      change 0 ≤ SBeta nr b b z at hSb
      by_contra hnot
      have : b-t < 0 := by linarith
      have hprod : 2*nr*(nr+2)*(1-b)*(b-t) < 0 :=
        mul_neg_of_pos_of_neg hslope this
      linarith
    have ht0 : 0 < t := lt_trans hr0 htr
    have hKt : 0 ≤ KBeta nr t b z :=
      kBeta_nonneg n hn t b z (le_of_lt ht0) htb (le_of_lt hb1)
        (le_of_lt hz) (le_of_eq hSt)
    have hch := kBeta_chord nr r t b z
    have hcorr : 0 < 4*nr^2*(nr+1)^2*(nr+2)*(b+z)*(1-b)^2*t*r*(t-r) := by
      positivity
    have hleft : 0 ≤ (t-r)*KBeta nr 0 b z := mul_nonneg (by linarith) hK0
    have hright : 0 ≤ r*KBeta nr t b z := mul_nonneg (le_of_lt hr0) hKt
    have htK : 0 < t*KBeta nr r b z := by nlinarith
    exact pos_of_mul_pos_right htK (le_of_lt ht0)

/-! ### The exceptional `n=4`, `B=B₀` face -/

theorem alpha_coefficient_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < 7*y^3-45*y^2+216*y+108 := by
  have hquad : 0 < 7*y^2-45*y+216 := by
    have hid : 28*(7*y^2-45*y+216) = (14*y-45)^2+4023 := by ring
    nlinarith [sq_nonneg (14*y-45)]
  nlinarith [mul_nonneg hy (le_of_lt hquad)]

theorem alpha_tail_pos (y : ℝ) (hy : 21 < y) :
    0 < 20*y^4-61*y^3-135*y^2-108*y-54 := by
  let t := y-21
  have ht : 0 < t := by dsimp [t]; linarith
  have hid : 20*y^4-61*y^3-135*y^2-108*y-54
      = 20*t^4+1619*t^3+48942*t^2+654399*t+3262842 := by
    dsimp [t]
    ring
  rw [hid]
  positivity

/-- Positivity of the exceptional boundary stationary-value numerator. -/
theorem rAlpha_nonneg_of_stationary (r b z : ℝ)
    (hr0 : 0 ≤ r) (hrb : r ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z)
    (hS : 0 < SSP.K2S4Renewal.SAlpha r b z) :
    0 < SSP.K2S4Renewal.RAlpha r b z := by
  have hb0 : 0 ≤ b := le_trans hr0 hrb
  by_cases hbzero : b = 0
  · subst b
    have hr : r = 0 := by linarith
    subst r
    unfold SSP.K2S4Renewal.SAlpha at hS
    unfold SSP.K2S4Renewal.RAlpha
    have hzpos : 0 < z := by
      by_contra hnot
      have : z = 0 := le_antisymm (le_of_not_gt hnot) hz
      subst z
      norm_num at hS
    have hzlarge : 50/3 < z := by
      nlinarith [mul_pos hzpos hS]
    have : 0 < 20*z^4-61*0*z^3-135*0^2*z^2-108*0^3*z-54*0^4 := by
      norm_num
      have hz2 : 0 < z^2 := sq_pos_of_pos hzpos
      have hz4 : z^4 = (z^2)^2 := by ring
      rw [hz4]
      positivity
    simpa using this
  · have hb : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbzero)
    let y := z/b
    have hy : 0 ≤ y := div_nonneg hz (le_of_lt hb)
    have hzy : z = b*y := by dsimp [y]; field_simp
    have hS0 : 0 < SSP.K2S4Renewal.SAlpha 0 b z := by
      have hid : SSP.K2S4Renewal.SAlpha r b z
          = SSP.K2S4Renewal.SAlpha 0 b z + 48*r*(b-1) := by
        unfold SSP.K2S4Renewal.SAlpha
        ring
      have hterm : 48*r*(b-1) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      nlinarith
    have hy21 : 21 < y := by
      have hs : 0 < b*(3*y^2-13*y-16)-(50*y+2) := by
        unfold SSP.K2S4Renewal.SAlpha at hS0
        rw [hzy] at hS0
        have hb2 : 0 < b^2 := sq_pos_of_pos hb
        nlinarith
      by_contra hnot
      have hyup : y ≤ 21 := le_of_not_gt hnot
      have hyprod : 0 ≤ y*(21-y) := mul_nonneg hy (by linarith)
      have hbound : 3*y^2-13*y-16 ≤ 50*y+2 := by nlinarith
      by_cases hq : 0 ≤ 3*y^2-13*y-16
      · have hmul : b*(3*y^2-13*y-16) ≤ 3*y^2-13*y-16 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hb1) hq]
        linarith
      · have hmul : b*(3*y^2-13*y-16) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hb0 (le_of_not_ge hq)
        nlinarith
    have hcoef : 0 < 324*b^3+648*b^2*z-135*b*z^2+21*z^3 := by
      have hc := alpha_coefficient_pos y hy
      rw [hzy]
      have hid : 324*b^3+648*b^2*(b*y)-135*b*(b*y)^2+21*(b*y)^3
          = 3*b^3*(7*y^3-45*y^2+216*y+108) := by ring
      rw [hid]
      positivity
    have htail := alpha_tail_pos y hy21
    have hR0 : 0 < SSP.K2S4Renewal.RAlpha 0 b z := by
      rw [hzy, SSP.K2S4Renewal.alpha_at_zero_scaled]
      positivity
    have hid : SSP.K2S4Renewal.RAlpha r b z
        = SSP.K2S4Renewal.RAlpha 0 b z
          + r*(324*b^3+648*b^2*z-135*b*z^2+21*z^3) := by
      unfold SSP.K2S4Renewal.RAlpha
      ring
    rw [hid]
    nlinarith [mul_nonneg hr0 (le_of_lt hcoef)]

/-! ## A two-dimensional convex-quadratic minimization lemma -/

noncomputable def quad2 (q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y : ℝ) : ℝ :=
  q₀ + g₁*x + g₂*y + h₁₁*x^2/2 + h₁₂*x*y + h₂₂*y^2/2

theorem quad1_nonneg (q g h t : ℝ) (hq : 0 ≤ q) (hh : 0 < h) (ht : 0 ≤ t)
    (hdisc : g < 0 → 0 ≤ 2*h*q-g^2) :
    0 ≤ q+g*t+h*t^2/2 := by
  rcases le_or_gt 0 g with hg | hg
  · have hgt : 0 ≤ g*t := mul_nonneg hg ht
    have hht : 0 ≤ h*t^2/2 := by positivity
    linarith
  · have hd := hdisc hg
    have hid : q+g*t+h*t^2/2
        = (2*h*q-g^2)/(2*h) + h/2*(t+g/h)^2 := by
      field_simp [ne_of_gt hh]
      ring
    rw [hid]
    have h₁ : 0 ≤ (2*h*q-g^2)/(2*h) := div_nonneg hd (by positivity)
    have h₂ : 0 ≤ h/2*(t+g/h)^2 := by positivity
    linarith

theorem quad1_pos (q g h t : ℝ) (hq : 0 < q) (hh : 0 < h) (ht : 0 ≤ t)
    (hdisc : g < 0 → 0 < 2*h*q-g^2) :
    0 < q+g*t+h*t^2/2 := by
  rcases le_or_gt 0 g with hg | hg
  · have hgt : 0 ≤ g*t := mul_nonneg hg ht
    have hht : 0 ≤ h*t^2/2 := by positivity
    linarith
  · have hd := hdisc hg
    have hid : q+g*t+h*t^2/2
        = (2*h*q-g^2)/(2*h)+h/2*(t+g/h)^2 := by
      field_simp [ne_of_gt hh]
      ring
    rw [hid]
    have h₁ : 0 < (2*h*q-g^2)/(2*h) := div_pos hd (by positivity)
    have h₂ : 0 ≤ h/2*(t+g/h)^2 := by positivity
    linarith

theorem quad2_min_y (q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y : ℝ) (hh₂₂ : h₂₂ ≠ 0) :
    quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y
      = quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x (-(g₂+h₁₂*x)/h₂₂)
        + h₂₂/2*(y+(g₂+h₁₂*x)/h₂₂)^2 := by
  unfold quad2
  field_simp [hh₂₂]
  ring

theorem quad2_reduced_diff (q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x c : ℝ) (hh₂₂ : h₂₂ ≠ 0) :
    quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x (-(g₂+h₁₂*x)/h₂₂)
      - quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ c (-(g₂+h₁₂*c)/h₂₂)
      = (x-c)/(2*h₂₂)
          *((h₁₁*h₂₂-h₁₂^2)*(x+c)+2*(h₂₂*g₁-h₁₂*g₂)) := by
  unfold quad2
  field_simp [hh₂₂]
  ring

/-- A positive-definite quadratic whose unconstrained stationary point has negative first
coordinate attains its minimum over the nonnegative quadrant on one of the two boundary faces. -/
theorem quad2_nonneg_on_quadrant
    (q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ : ℝ)
    (hh₂₂ : 0 < h₂₂) (hdet : 0 < h₁₁*h₂₂-h₁₂^2)
    (hstar : h₁₂*g₂-h₂₂*g₁ < 0)
    (hface1 : ∀ y, 0 ≤ y → 0 ≤ quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ 0 y)
    (hface2 : ∀ x, 0 ≤ x → 0 ≤ quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x 0)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y := by
  let d := g₂+h₁₂*x
  rcases le_or_gt 0 d with hd | hd
  · have hid : quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y
        = quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x 0 + d*y + h₂₂*y^2/2 := by
      dsimp [d]
      unfold quad2
      ring
    rw [hid]
    have h₀ := hface2 x hx
    have h₁ : 0 ≤ d*y := mul_nonneg hd hy
    have h₂ : 0 ≤ h₂₂*y^2/2 := by positivity
    linarith
  · have hdneg : d < 0 := hd
    have hsq : 0 ≤ h₂₂/2*(y+(g₂+h₁₂*x)/h₂₂)^2 := by positivity
    have hmin := quad2_min_y q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y (ne_of_gt hh₂₂)
    rw [hmin]
    apply add_nonneg
    · rcases le_total g₂ 0 with hg₂ | hg₂
      · let y₀ := -g₂/h₂₂
        have hy₀ : 0 ≤ y₀ := div_nonneg (neg_nonneg.mpr hg₂) (le_of_lt hh₂₂)
        have hbase := hface1 y₀ hy₀
        dsimp [y₀] at hbase
        have hdiff := quad2_reduced_diff q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x 0 (ne_of_gt hh₂₂)
        norm_num at hdiff
        have heq : (-(h₁₂*x)+ -g₂)/h₂₂ = -(g₂+h₁₂*x)/h₂₂ := by ring
        rw [heq] at hdiff
        have hlin : 0 < h₂₂*g₁-h₁₂*g₂ := by linarith
        have hbr : 0 < (h₁₁*h₂₂-h₁₂^2)*(x+0)+2*(h₂₂*g₁-h₁₂*g₂) := by
          have : 0 ≤ (h₁₁*h₂₂-h₁₂^2)*x := mul_nonneg (le_of_lt hdet) hx
          linarith
        have hcoef : 0 ≤ x/(2*h₂₂) := by positivity
        have hprod := mul_nonneg hcoef (le_of_lt hbr)
        nlinarith
      · have hh₁₂ : h₁₂ < 0 := by
          by_contra hnot
          have : 0 ≤ h₁₂ := le_of_not_gt hnot
          have : 0 < d := by dsimp [d]; nlinarith [mul_nonneg this hx]
          linarith
        let c := -g₂/h₁₂
        have hc : 0 ≤ c := by
          dsimp [c]
          rw [div_eq_mul_inv]
          exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hg₂)
            (le_of_lt (by simpa [one_div] using one_div_neg.mpr hh₁₂))
        have hcx : c ≤ x := by
          have hmul : h₁₂*x < -g₂ := by dsimp [d] at hdneg; linarith
          have hceq : h₁₂*c = -g₂ := by
            dsimp [c]
            field_simp [ne_of_lt hh₁₂]
          by_contra hnot
          have hxc' : x < c := lt_of_not_ge hnot
          have hmul' := mul_lt_mul_of_neg_left hxc' hh₁₂
          nlinarith
        have hdc : g₂+h₁₂*c = 0 := by
          dsimp [c]
          field_simp [ne_of_lt hh₁₂]
          ring
        have hbase := hface2 c hc
        have hdiff := quad2_reduced_diff q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x c (ne_of_gt hh₂₂)
        rw [hdc] at hdiff
        norm_num at hdiff
        have heq : (-(h₁₂*x)+ -g₂)/h₂₂ = -(g₂+h₁₂*x)/h₂₂ := by ring
        rw [heq] at hdiff
        have hlin : 0 < h₂₂*g₁-h₁₂*g₂ := by linarith
        have hxc : 0 ≤ x-c := sub_nonneg.mpr hcx
        have hsum : 0 ≤ x+c := by linarith
        have hbr : 0 < (h₁₁*h₂₂-h₁₂^2)*(x+c)+2*(h₂₂*g₁-h₁₂*g₂) := by
          have : 0 ≤ (h₁₁*h₂₂-h₁₂^2)*(x+c) := mul_nonneg (le_of_lt hdet) hsum
          linarith
        have hcoef : 0 ≤ (x-c)/(2*h₂₂) := by positivity
        have hprod := mul_nonneg hcoef (le_of_lt hbr)
        nlinarith
    · exact hsq

/-- Strict version of `quad2_nonneg_on_quadrant`, when both boundary faces are positive. -/
theorem quad2_pos_on_quadrant
    (q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ : ℝ)
    (hh₂₂ : 0 < h₂₂) (hdet : 0 < h₁₁*h₂₂-h₁₂^2)
    (hstar : h₁₂*g₂-h₂₂*g₁ < 0)
    (hface1 : ∀ y, 0 ≤ y → 0 < quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ 0 y)
    (hface2 : ∀ x, 0 ≤ x → 0 < quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x 0)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 < quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y := by
  let d := g₂+h₁₂*x
  rcases le_or_gt 0 d with hd | hd
  · have hid : quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y
        = quad2 q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x 0+d*y+h₂₂*y^2/2 := by
      dsimp [d]
      unfold quad2
      ring
    rw [hid]
    have h₀ := hface2 x hx
    have h₁ : 0 ≤ d*y := mul_nonneg hd hy
    have h₂ : 0 ≤ h₂₂*y^2/2 := by positivity
    linarith
  · have hsq : 0 ≤ h₂₂/2*(y+(g₂+h₁₂*x)/h₂₂)^2 := by positivity
    have hmin := quad2_min_y q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x y (ne_of_gt hh₂₂)
    rw [hmin]
    apply add_pos_of_pos_of_nonneg
    · rcases le_total g₂ 0 with hg₂ | hg₂
      · let y₀ := -g₂/h₂₂
        have hy₀ : 0 ≤ y₀ := div_nonneg (neg_nonneg.mpr hg₂) (le_of_lt hh₂₂)
        have hbase := hface1 y₀ hy₀
        have hdiff := quad2_reduced_diff q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x 0 (ne_of_gt hh₂₂)
        norm_num at hdiff
        have heq : (-(h₁₂*x)+ -g₂)/h₂₂ = -(g₂+h₁₂*x)/h₂₂ := by ring
        rw [heq] at hdiff
        have hlin : 0 < h₂₂*g₁-h₁₂*g₂ := by linarith
        have hbr : 0 < (h₁₁*h₂₂-h₁₂^2)*(x+0)+2*(h₂₂*g₁-h₁₂*g₂) := by
          have : 0 ≤ (h₁₁*h₂₂-h₁₂^2)*x := mul_nonneg (le_of_lt hdet) hx
          linarith
        have hcoef : 0 ≤ x/(2*h₂₂) := by positivity
        have hprod := mul_nonneg hcoef (le_of_lt hbr)
        nlinarith
      · have hh₁₂ : h₁₂ < 0 := by
          by_contra hnot
          have hh₁₂non : 0 ≤ h₁₂ := le_of_not_gt hnot
          have : 0 < d := by dsimp [d]; nlinarith [mul_nonneg hh₁₂non hx]
          linarith
        let c := -g₂/h₁₂
        have hc : 0 ≤ c := by
          dsimp [c]
          rw [div_eq_mul_inv]
          exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hg₂)
            (le_of_lt (by simpa [one_div] using one_div_neg.mpr hh₁₂))
        have hcx : c ≤ x := by
          have hmul : h₁₂*x < -g₂ := by dsimp [d] at hd; linarith
          have hceq : h₁₂*c = -g₂ := by
            dsimp [c]
            field_simp [ne_of_lt hh₁₂]
          by_contra hnot
          have hxc' : x < c := lt_of_not_ge hnot
          have hmul' := mul_lt_mul_of_neg_left hxc' hh₁₂
          nlinarith
        have hdc : g₂+h₁₂*c = 0 := by
          dsimp [c]
          field_simp [ne_of_lt hh₁₂]
          ring
        have hbase := hface2 c hc
        have hdiff := quad2_reduced_diff q₀ g₁ g₂ h₁₁ h₁₂ h₂₂ x c (ne_of_gt hh₂₂)
        rw [hdc] at hdiff
        norm_num at hdiff
        have heq : (-(h₁₂*x)+ -g₂)/h₂₂ = -(g₂+h₁₂*x)/h₂₂ := by ring
        rw [heq] at hdiff
        have hlin : 0 < h₂₂*g₁-h₁₂*g₂ := by linarith
        have hxc : 0 ≤ x-c := sub_nonneg.mpr hcx
        have hsum : 0 ≤ x+c := by linarith
        have hbr : 0 < (h₁₁*h₂₂-h₁₂^2)*(x+c)+2*(h₂₂*g₁-h₁₂*g₂) := by
          have : 0 ≤ (h₁₁*h₂₂-h₁₂^2)*(x+c) := mul_nonneg (le_of_lt hdet) hsum
          linarith
        have hcoef : 0 ≤ (x-c)/(2*h₂₂) := by positivity
        have hprod := mul_nonneg hcoef (le_of_lt hbr)
        nlinarith
    · exact hsq

/-! ## Assembly of the normalized renewal quadratic -/

/-- The normalized gradient in the `A` direction at the lower corner. -/
noncomputable def gAlpha (n r b z : ℝ) : ℝ :=
  (b-r)*(1-b) / ((1-r)^2*(n-1)) * SAlpha n r b z

/-- The normalized gradient in the `B` direction at the lower corner. -/
noncomputable def gBeta (n r b z : ℝ) : ℝ := SBeta n r b z / (n-1)

/-- The normalized `AA` entry of the Hessian. -/
noncomputable def hAlphaAlpha (n r b z : ℝ) : ℝ :=
  2*(b-r)*(1-b)^2 / (n*(1-r)^4)
    * (n*(n+2)*r+b+(n+1)^2*z)

/-- The normalized `AB` entry of the Hessian. -/
noncomputable def hAlphaBeta (n r b _z : ℝ) : ℝ :=
  -2*(n+2)*(b-r)*(1-b)/(1-r)^2

/-- The normalized `BB` entry of the Hessian. -/
noncomputable def hBetaBeta (n b z : ℝ) : ℝ :=
  2*((n+1)^2*b+z)/(n*z)

/-- The renewal gap after translating the feasible lower corner to the origin. -/
noncomputable def renewalQuad (n r b z da db : ℝ) : ℝ :=
  quad2 (Phi n r b z/(n-1)^2)
    (gAlpha n r b z) (gBeta n r b z)
    (hAlphaAlpha n r b z) (hAlphaBeta n r b z)
    (hBetaBeta n b z) da db

theorem beta_face_discriminant (n r b z : ℝ) (hn : n ≠ 0) (hn1 : n ≠ 1)
    (hz : z ≠ 0) :
    2*hBetaBeta n b z*(Phi n r b z/(n-1)^2) - (gBeta n r b z)^2
      = KBeta n r b z/(n*z*(n-1)^2) := by
  unfold hBetaBeta gBeta KBeta MBeta
  field_simp
  ring

theorem hessian_det_factor (n r b z : ℝ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hr : r ≠ 1) :
    hAlphaAlpha n r b z * hBetaBeta n b z - (hAlphaBeta n r b z)^2
      = 4*(b-r)*(1-b)^2*(b+z)*(n+1)^2*(b+n^2*r+2*n*r+z)
          /(n^2*z*(1-r)^4) := by
  unfold hAlphaAlpha hBetaBeta hAlphaBeta
  field_simp
  ring

theorem alpha_face_discriminant_four (r b z : ℝ) (hr : r ≠ 1) :
    2*hAlphaAlpha 4 r b z*(Phi 4 r b z/9) - (gAlpha 4 r b z)^2
      = 5*(b-r)*(1-b)^2*(b+z)*SSP.K2S4Renewal.RAlpha r b z
          /(9*(1-r)^4) := by
  have hphi : Phi 4 r b z = 2*SSP.K2S4Renewal.Phi r b z := by
    unfold Phi SSP.K2S4Renewal.Phi
    ring
  have hs : SAlpha 4 r b z = -SSP.K2S4Renewal.SAlpha r b z := by
    unfold SAlpha SSP.K2S4Renewal.SAlpha
    ring
  rw [hphi]
  unfold hAlphaAlpha gAlpha
  rw [hs]
  have hedge := SSP.K2S4Renewal.alpha_edge_factor r b z
  calc
    2 * (2 * (b-r) * (1-b)^2 / (4*(1-r)^4)
          * (4*(4+2)*r+b+(4+1)^2*z))
          * (2*SSP.K2S4Renewal.Phi r b z/9)
        - ((b-r)*(1-b)/((1-r)^2*(4-1))
          * -SSP.K2S4Renewal.SAlpha r b z)^2
        = (b-r)*(1-b)^2/(9*(1-r)^4)
            * (2*(25*(b+z)-24*(b-r))*SSP.K2S4Renewal.Phi r b z
              -(b-r)*(SSP.K2S4Renewal.SAlpha r b z)^2) := by
            field_simp [hr]
            ring
    _ = (b-r)*(1-b)^2/(9*(1-r)^4)
          * (5*(b+z)*SSP.K2S4Renewal.RAlpha r b z) := by rw [hedge]
    _ = 5*(b-r)*(1-b)^2*(b+z)*SSP.K2S4Renewal.RAlpha r b z
          /(9*(1-r)^4) := by ring

/-- The positive polynomial used to exclude an interior stationary point, in normalized
coordinates. -/
noncomputable def interiorRNorm (n r b z : ℝ) : ℝ :=
  InteriorR n r (1-r) (z*(1-r)/(1-b))
    ((b-r)/(1-r)) ((1-b)/(1-r))

theorem interior_stationary_factor (n r b z : ℝ)
    (hn : n ≠ 0) (hn1 : n ≠ 1) (hz : z ≠ 0)
    (hr : r ≠ 1) (hb : b ≠ 1) :
    hAlphaBeta n r b z * gBeta n r b z
        - hBetaBeta n b z * gAlpha n r b z
      = -2*(b-r)*(1-b)*(b+z)*(n+1)
          /(n*z*(n-1)*(1-r)^2) * interiorRNorm n r b z := by
  unfold hAlphaBeta gBeta hBetaBeta gAlpha interiorRNorm
  unfold SBeta SAlpha InteriorR InteriorR0 InteriorR1 InteriorR2
  field_simp
  ring

/-- The translated, normalized renewal gap is nonnegative in the nondegenerate parameter
region.  This theorem assembles all corner, boundary, and interior certificates above. -/
theorem renewalQuad_nonneg (n : ℕ) (hn : 4 ≤ n) (r b z da db : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 < z)
    (hda : 0 ≤ da) (hdb : 0 ≤ db) :
    0 ≤ renewalQuad n r b z da db := by
  let nr : ℝ := n
  have hnr4 : 4 ≤ nr := by dsimp [nr]; exact_mod_cast hn
  have hnr0 : 0 < nr := by linarith
  have hnr1 : 1 < nr := by linarith
  have hr1 : r < 1 := lt_trans hrb hb1
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hcorner : 0 ≤ Phi nr r b z := by
    exact corner_nonneg n hn r b z (le_of_lt hr0) (le_of_lt hrb) (le_of_lt hb1)
      (le_of_lt hz)
  have hq0 : 0 ≤ Phi nr r b z/(nr-1)^2 := by positivity
  have hhbb : 0 < hBetaBeta nr b z := by
    unfold hBetaBeta
    positivity
  have hhaa : 0 < hAlphaAlpha nr r b z := by
    unfold hAlphaAlpha
    positivity
  have hdet : 0 < hAlphaAlpha nr r b z*hBetaBeta nr b z
      -(hAlphaBeta nr r b z)^2 := by
    rw [hessian_det_factor nr r b z (ne_of_gt hnr0) (ne_of_gt hz) (ne_of_lt hr1)]
    positivity
  have hR : 0 < interiorRNorm nr r b z := by
    unfold interiorRNorm
    apply interiorR_pos nr r (1-r) (z*(1-r)/(1-b))
      ((b-r)/(1-r)) ((1-b)/(1-r)) hnr4
    all_goals positivity
  have hstar : hAlphaBeta nr r b z*gBeta nr r b z
      -hBetaBeta nr b z*gAlpha nr r b z < 0 := by
    rw [interior_stationary_factor nr r b z (ne_of_gt hnr0) (ne_of_gt hnr1)
      (ne_of_gt hz) (ne_of_lt hr1) (ne_of_lt hb1)]
    have hfac : 0 < 2*(b-r)*(1-b)*(b+z)*(nr+1)
        /(nr*z*(nr-1)*(1-r)^2) := by positivity
    have heq : -2*(b-r)*(1-b)*(b+z)*(nr+1)
        /(nr*z*(nr-1)*(1-r)^2)
        = -(2*(b-r)*(1-b)*(b+z)*(nr+1)
          /(nr*z*(nr-1)*(1-r)^2)) := by ring
    rw [heq]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfac) hR
  have hfaceBeta : ∀ t, 0 ≤ t →
      0 ≤ quad2 (Phi nr r b z/(nr-1)^2)
        (gAlpha nr r b z) (gBeta nr r b z)
        (hAlphaAlpha nr r b z) (hAlphaBeta nr r b z)
        (hBetaBeta nr b z) 0 t := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_nonneg (Phi nr r b z/(nr-1)^2) (gBeta nr r b z)
      (hBetaBeta nr b z) t hq0 hhbb ht
    intro hg
    have hS : SBeta nr r b z ≤ 0 := by
      unfold gBeta at hg
      have hden : 0 < nr-1 := by linarith
      rw [div_neg_iff] at hg
      rcases hg with hg | hg
      · linarith
      · exact le_of_lt hg.1
    have hK := kBeta_nonneg n hn r b z (le_of_lt hr0) (le_of_lt hrb)
      (le_of_lt hb1) (le_of_lt hz) hS
    rw [beta_face_discriminant nr r b z (ne_of_gt hnr0) (ne_of_gt hnr1)
      (ne_of_gt hz)]
    positivity
  have hfaceAlpha : ∀ t, 0 ≤ t →
      0 ≤ quad2 (Phi nr r b z/(nr-1)^2)
        (gAlpha nr r b z) (gBeta nr r b z)
        (hAlphaAlpha nr r b z) (hAlphaBeta nr r b z)
        (hBetaBeta nr b z) t 0 := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_nonneg (Phi nr r b z/(nr-1)^2) (gAlpha nr r b z)
      (hAlphaAlpha nr r b z) t hq0 hhaa ht
    intro hg
    by_cases hfour : n = 4
    · have hnreq : nr = 4 := by simp [nr, hfour]
      rw [hnreq] at hg ⊢
      norm_num
      have holdS : 0 < SSP.K2S4Renewal.SAlpha r b z := by
        have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(4-1:ℝ)) := by positivity
        have hs : SAlpha 4 r b z = -SSP.K2S4Renewal.SAlpha r b z := by
          unfold SAlpha SSP.K2S4Renewal.SAlpha
          ring
        unfold gAlpha at hg
        rw [hs] at hg
        nlinarith [mul_pos hpre (show 0 < SSP.K2S4Renewal.SAlpha r b z by
          by_contra hnot
          have : SSP.K2S4Renewal.SAlpha r b z ≤ 0 := le_of_not_gt hnot
          have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpre) this
          linarith)]
      have hRA := rAlpha_nonneg_of_stationary r b z (le_of_lt hr0) (le_of_lt hrb)
        (le_of_lt hb1) (le_of_lt hz) holdS
      have hid := alpha_face_discriminant_four r b z (ne_of_lt hr1)
      have hnon : 0 ≤ 5*(b-r)*(1-b)^2*(b+z)*SSP.K2S4Renewal.RAlpha r b z
          /(9*(1-r)^4) := by positivity
      nlinarith
    · have hn5 : 5 ≤ n := by omega
      have hn5r : (5:ℝ) ≤ nr := by dsimp [nr]; exact_mod_cast hn5
      have hSA := sAlpha_pos_of_five nr r b z hn5r (le_of_lt hr0) (le_of_lt hb0)
        (le_of_lt hb1) (le_of_lt hz) (by positivity)
      have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(nr-1)) := by positivity
      unfold gAlpha at hg
      nlinarith [mul_pos hpre hSA]
  unfold renewalQuad
  exact quad2_nonneg_on_quadrant
    (Phi nr r b z/(nr-1)^2) (gAlpha nr r b z) (gBeta nr r b z)
    (hAlphaAlpha nr r b z) (hAlphaBeta nr r b z) (hBetaBeta nr b z)
    hhbb hdet hstar hfaceBeta hfaceAlpha da db hda hdb

/-- Strict form of the normalized renewal inequality in the genuine routing region. -/
theorem renewalQuad_pos (n : ℕ) (hn : 4 ≤ n) (r b z da db : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 < z)
    (hda : 0 ≤ da) (hdb : 0 ≤ db) :
    0 < renewalQuad n r b z da db := by
  let nr : ℝ := n
  have hnr4 : 4 ≤ nr := by dsimp [nr]; exact_mod_cast hn
  have hnr0 : 0 < nr := by linarith
  have hnr1 : 1 < nr := by linarith
  have hr1 : r < 1 := lt_trans hrb hb1
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hcorner : 0 < Phi nr r b z :=
    corner_pos_interior n hn r b z hr0 hrb hb1 (le_of_lt hz)
  have hq0 : 0 < Phi nr r b z/(nr-1)^2 := by positivity
  have hhbb : 0 < hBetaBeta nr b z := by unfold hBetaBeta; positivity
  have hhaa : 0 < hAlphaAlpha nr r b z := by unfold hAlphaAlpha; positivity
  have hdet : 0 < hAlphaAlpha nr r b z*hBetaBeta nr b z
      -(hAlphaBeta nr r b z)^2 := by
    rw [hessian_det_factor nr r b z (ne_of_gt hnr0) (ne_of_gt hz) (ne_of_lt hr1)]
    positivity
  have hR : 0 < interiorRNorm nr r b z := by
    unfold interiorRNorm
    apply interiorR_pos nr r (1-r) (z*(1-r)/(1-b))
      ((b-r)/(1-r)) ((1-b)/(1-r)) hnr4
    all_goals positivity
  have hstar : hAlphaBeta nr r b z*gBeta nr r b z
      -hBetaBeta nr b z*gAlpha nr r b z < 0 := by
    rw [interior_stationary_factor nr r b z (ne_of_gt hnr0) (ne_of_gt hnr1)
      (ne_of_gt hz) (ne_of_lt hr1) (ne_of_lt hb1)]
    have hfac : 0 < 2*(b-r)*(1-b)*(b+z)*(nr+1)
        /(nr*z*(nr-1)*(1-r)^2) := by positivity
    have heq : -2*(b-r)*(1-b)*(b+z)*(nr+1)
        /(nr*z*(nr-1)*(1-r)^2)
        = -(2*(b-r)*(1-b)*(b+z)*(nr+1)
          /(nr*z*(nr-1)*(1-r)^2)) := by ring
    rw [heq]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfac) hR
  have hfaceBeta : ∀ t, 0 ≤ t →
      0 < quad2 (Phi nr r b z/(nr-1)^2)
        (gAlpha nr r b z) (gBeta nr r b z)
        (hAlphaAlpha nr r b z) (hAlphaBeta nr r b z)
        (hBetaBeta nr b z) 0 t := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_pos (Phi nr r b z/(nr-1)^2) (gBeta nr r b z)
      (hBetaBeta nr b z) t hq0 hhbb ht
    intro hg
    have hS : SBeta nr r b z < 0 := by
      unfold gBeta at hg
      rw [div_neg_iff] at hg
      rcases hg with hg | hg
      · linarith
      · exact hg.1
    have hK := kBeta_pos_interior n hn r b z hr0 hrb hb1 hz hS
    rw [beta_face_discriminant nr r b z (ne_of_gt hnr0) (ne_of_gt hnr1)
      (ne_of_gt hz)]
    positivity
  have hfaceAlpha : ∀ t, 0 ≤ t →
      0 < quad2 (Phi nr r b z/(nr-1)^2)
        (gAlpha nr r b z) (gBeta nr r b z)
        (hAlphaAlpha nr r b z) (hAlphaBeta nr r b z)
        (hBetaBeta nr b z) t 0 := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_pos (Phi nr r b z/(nr-1)^2) (gAlpha nr r b z)
      (hAlphaAlpha nr r b z) t hq0 hhaa ht
    intro hg
    by_cases hfour : n = 4
    · have hnreq : nr = 4 := by simp [nr, hfour]
      rw [hnreq] at hg ⊢
      norm_num
      have holdS : 0 < SSP.K2S4Renewal.SAlpha r b z := by
        have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(4-1:ℝ)) := by positivity
        have hs : SAlpha 4 r b z = -SSP.K2S4Renewal.SAlpha r b z := by
          unfold SAlpha SSP.K2S4Renewal.SAlpha
          ring
        unfold gAlpha at hg
        rw [hs] at hg
        by_contra hnot
        have holdnon : SSP.K2S4Renewal.SAlpha r b z ≤ 0 := le_of_not_gt hnot
        have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpre) holdnon
        linarith
      have hRA := rAlpha_nonneg_of_stationary r b z (le_of_lt hr0) (le_of_lt hrb)
        (le_of_lt hb1) (le_of_lt hz) holdS
      have hid := alpha_face_discriminant_four r b z (ne_of_lt hr1)
      have hpos : 0 < 5*(b-r)*(1-b)^2*(b+z)*SSP.K2S4Renewal.RAlpha r b z
          /(9*(1-r)^4) := by positivity
      nlinarith
    · have hn5 : 5 ≤ n := by omega
      have hn5r : (5:ℝ) ≤ nr := by dsimp [nr]; exact_mod_cast hn5
      have hSA := sAlpha_pos_of_five nr r b z hn5r (le_of_lt hr0) (le_of_lt hb0)
        (le_of_lt hb1) (le_of_lt hz) (by positivity)
      have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(nr-1)) := by positivity
      unfold gAlpha at hg
      nlinarith [mul_pos hpre hSA]
  unfold renewalQuad
  exact quad2_pos_on_quadrant
    (Phi nr r b z/(nr-1)^2) (gAlpha nr r b z) (gBeta nr r b z)
    (hAlphaAlpha nr r b z) (hAlphaBeta nr r b z) (hBetaBeta nr b z)
    hhbb hdet hstar hfaceBeta hfaceAlpha da db hda hdb

/-- Strict positivity on the `B=B₀` face, also valid at `z=0`. -/
theorem renewalQuad_alpha_face_pos (n : ℕ) (hn : 4 ≤ n) (r b z da : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 ≤ z)
    (hda : 0 ≤ da) :
    0 < renewalQuad n r b z da 0 := by
  let nr : ℝ := n
  have hnr4 : 4 ≤ nr := by dsimp [nr]; exact_mod_cast hn
  have hnr0 : 0 < nr := by linarith
  have hnr1 : 1 < nr := by linarith
  have hr1 : r < 1 := lt_trans hrb hb1
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hcorner := corner_pos_interior n hn r b z hr0 hrb hb1 hz
  have hq0 : 0 < Phi nr r b z/(nr-1)^2 := by positivity
  have hhaa : 0 < hAlphaAlpha nr r b z := by unfold hAlphaAlpha; positivity
  have hdisc : gAlpha nr r b z < 0 →
      0 < 2*hAlphaAlpha nr r b z*(Phi nr r b z/(nr-1)^2)
        -(gAlpha nr r b z)^2 := by
    intro hg
    by_cases hfour : n = 4
    · have hnreq : nr=4 := by simp [nr, hfour]
      rw [hnreq] at hg ⊢
      norm_num
      have holdS : 0 < SSP.K2S4Renewal.SAlpha r b z := by
        have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(4-1:ℝ)) := by positivity
        have hs : SAlpha 4 r b z = -SSP.K2S4Renewal.SAlpha r b z := by
          unfold SAlpha SSP.K2S4Renewal.SAlpha
          ring
        unfold gAlpha at hg
        rw [hs] at hg
        by_contra hnot
        have holdnon : SSP.K2S4Renewal.SAlpha r b z ≤ 0 := le_of_not_gt hnot
        have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpre) holdnon
        linarith
      have hRA := rAlpha_nonneg_of_stationary r b z (le_of_lt hr0) (le_of_lt hrb)
        (le_of_lt hb1) hz holdS
      have hid := alpha_face_discriminant_four r b z (ne_of_lt hr1)
      have hpos : 0 < 5*(b-r)*(1-b)^2*(b+z)*SSP.K2S4Renewal.RAlpha r b z
          /(9*(1-r)^4) := by positivity
      nlinarith
    · have hn5 : 5 ≤ n := by omega
      have hn5r : (5:ℝ) ≤ nr := by dsimp [nr]; exact_mod_cast hn5
      have hSA := sAlpha_pos_of_five nr r b z hn5r (le_of_lt hr0) (le_of_lt hb0)
        (le_of_lt hb1) hz (by positivity)
      have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(nr-1)) := by positivity
      unfold gAlpha at hg
      nlinarith [mul_pos hpre hSA]
  have hface := quad1_pos (Phi nr r b z/(nr-1)^2) (gAlpha nr r b z)
    (hAlphaAlpha nr r b z) da hq0 hhaa hda hdisc
  unfold renewalQuad quad2
  norm_num
  exact hface

/-! ## The renewal moment formulas and their normalization -/

noncomputable def kernelM1 (x a : ℝ) : ℝ := x+a
noncomputable def kernelM2 (x a A : ℝ) : ℝ := 2*x^2+2*x*a+A
noncomputable def kernelM3 (x a A C : ℝ) : ℝ := 6*x^3+6*x^2*a+3*x*A+C

noncomputable def renewalX1 (x u v p q : ℝ) : ℝ :=
  q*kernelM1 x v+p*kernelM1 x u

noncomputable def renewalX2 (x u v p q A B : ℝ) : ℝ :=
  q^2*kernelM2 x v B+p*q*kernelM2 x u A
    +2*p^2*(kernelM1 x u)^2+2*p*q*kernelM1 x v*kernelM1 x u

noncomputable def renewalX3 (x u v p q A B C D : ℝ) : ℝ :=
  q^3*kernelM3 x v B D+p*q^2*kernelM3 x u A C
    +3*p*q^2*kernelM2 x v B*kernelM1 x u
    +3*p*q^2*kernelM1 x v*kernelM2 x u A
    +6*p^2*q*kernelM1 x v*(kernelM1 x u)^2
    +6*p^2*q*kernelM2 x u A*kernelM1 x u
    +6*p^3*(kernelM1 x u)^3

noncomputable def renewalGap (n x u v p q A B C D : ℝ) : ℝ :=
  (n+1)*renewalX1 x u v p q*renewalX3 x u v p q A B C D
    -(n+2)*(renewalX2 x u v p q A B)^2

noncomputable def renewalGapSub (n x u v p q A B : ℝ) : ℝ :=
  renewalGap n x u v p q A B ((n+1)/n*A^2/u) ((n+1)/n*B^2/v)

/-- Exact change of variables from the renewal moments to the translated normalized
quadratic used above. -/
theorem renewalGap_normalization (n x u v p q A B : ℝ)
    (hn : n ≠ 0) (hn1 : n ≠ 1) (hu : u ≠ 0) (hv : v ≠ 0)
    (hl : x+u ≠ 0) (hpq : p+q=1) :
    renewalGapSub n x u v p q A B
      = (x+u)^4 * renewalQuad n
          (x/(x+u)) (p+q*(x/(x+u))) (q*v/(x+u))
          (A/(x+u)^2-n/(n-1)*(u/(x+u))^2)
          (q^2*B/(x+u)^2-n/(n-1)*(q*v/(x+u))^2) := by
  have hp : p = 1-q := by linarith
  unfold renewalGapSub renewalGap renewalX1 renewalX2 renewalX3
  unfold kernelM1 kernelM2 kernelM3 renewalQuad quad2
  unfold gAlpha gBeta hAlphaAlpha hAlphaBeta hBetaBeta
  unfold Phi SAlpha SBeta
  rw [hp]
  field_simp [hn, hn1, hu, hv, hl]
  ring

noncomputable def renewalGapSubVZero (n x u p q A : ℝ) : ℝ :=
  renewalGap n x u 0 p q A 0 ((n+1)/n*A^2/u) 0

theorem renewalGap_normalization_vzero (n x u p q A : ℝ)
    (hn : n ≠ 0) (hn1 : n ≠ 1) (hu : u ≠ 0)
    (hl : x+u ≠ 0) (hpq : p+q=1) :
    renewalGapSubVZero n x u p q A
      = (x+u)^4*renewalQuad n
          (x/(x+u)) (p+q*(x/(x+u))) 0
          (A/(x+u)^2-n/(n-1)*(u/(x+u))^2) 0 := by
  have hp : p=1-q := by linarith
  unfold renewalGapSubVZero renewalGap renewalX1 renewalX2 renewalX3
  unfold kernelM1 kernelM2 kernelM3 renewalQuad quad2
  unfold gAlpha gBeta hAlphaAlpha hAlphaBeta hBetaBeta
  unfold Phi SAlpha SBeta
  rw [hp]
  field_simp [hn, hn1, hu, hl]
  ring

theorem renewalGap_vzero_third_slack (n x u p q A C : ℝ)
    (hn : n ≠ 0) (hu : u ≠ 0) :
    renewalGap n x u 0 p q A 0 C 0
      = renewalGapSubVZero n x u p q A
        +(n+1)*renewalX1 x u 0 p q*p*q^2*(C-(n+1)/n*A^2/u) := by
  unfold renewalGapSubVZero renewalGap renewalX1 renewalX2 renewalX3
  unfold kernelM1 kernelM2 kernelM3
  field_simp [hn, hu]
  ring

/-- Reintroducing the two third-moment slacks changes the gap by a manifestly
nonnegative linear term. -/
theorem renewalGap_third_slacks (n x u v p q A B C D : ℝ)
    (hn : n ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    renewalGap n x u v p q A B C D
      = renewalGapSub n x u v p q A B
        +(n+1)*renewalX1 x u v p q
          *(p*q^2*(C-(n+1)/n*A^2/u)+q^3*(D-(n+1)/n*B^2/v)) := by
  unfold renewalGapSub renewalGap renewalX1 renewalX2 renewalX3
  unfold kernelM1 kernelM2 kernelM3
  field_simp [hn, hu, hv]
  ring

/-- The full two-kernel renewal inequality in the nondegenerate case.  Its hypotheses are
exactly the two moment inequalities required of each excursion kernel. -/
theorem renewalGap_nonneg (n : ℕ) (hn : 4 ≤ n)
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (n:ℝ)/(n-1)*u^2 ≤ A) (hB : (n:ℝ)/(n-1)*v^2 ≤ B)
    (hC : (n+1)*A^2 ≤ (n:ℝ)*u*C)
    (hD : (n+1)*B^2 ≤ (n:ℝ)*v*D) :
    0 ≤ renewalGap n x u v p q A B C D := by
  let nr : ℝ := n
  let l := x+u
  let r := x/l
  let b := p+q*r
  let z := q*v/l
  let da := A/l^2-nr/(nr-1)*(u/l)^2
  let db := q^2*B/l^2-nr/(nr-1)*z^2
  have hnr0 : 0 < nr := by dsimp [nr]; positivity
  have hnr1 : 1 < nr := by dsimp [nr]; exact_mod_cast (show 1 < n by omega)
  have hl : 0 < l := by dsimp [l]; linarith
  have h1r : 0 < 1-r := by
    have hid : 1-r = u/l := by
      dsimp [r, l]
      field_simp [ne_of_gt (show 0 < x+u by linarith)]
      ring
    rw [hid]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hbr : b-r = p*(1-r) := by
    have hpform : p = 1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hrb : r < b := by
    rw [← sub_pos, hbr]
    positivity
  have h1b : 1-b = q*(1-r) := by
    have hpform : p = 1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hb1 : b < 1 := by
    rw [← sub_pos, h1b]
    positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hda : 0 ≤ da := by
    have hbase : 0 ≤ A-nr/(nr-1)*u^2 := by
      dsimp [nr]
      linarith
    have hid : da = (A-nr/(nr-1)*u^2)/l^2 := by
      dsimp [da]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-nr/(nr-1)*v^2 := by
      dsimp [nr]
      linarith
    have hid : db = q^2/l^2*(B-nr/(nr-1)*v^2) := by
      dsimp [db, z]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hquad := renewalQuad_nonneg n hn r b z da db hr0 hrb hb1 hz hda hdb
  have hnorm := renewalGap_normalization nr x u v p q A B (ne_of_gt hnr0)
    (ne_of_gt hnr1) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) hpq
  have hsub : 0 ≤ renewalGapSub nr x u v p q A B := by
    rw [hnorm]
    exact mul_nonneg (by positivity) hquad
  have hdu : 0 ≤ C-(nr+1)/nr*A^2/u := by
    have hden : 0 < nr*u := mul_pos hnr0 hu
    have hquot : (nr+1)*A^2/(nr*u) ≤ C := by
      rw [div_le_iff₀ hden]
      dsimp [nr] at hC ⊢
      nlinarith
    have hid : (nr+1)/nr*A^2/u = (nr+1)*A^2/(nr*u) := by
      field_simp [ne_of_gt hnr0, ne_of_gt hu]
    rw [hid]
    linarith
  have hdv : 0 ≤ D-(nr+1)/nr*B^2/v := by
    have hden : 0 < nr*v := mul_pos hnr0 hv
    have hquot : (nr+1)*B^2/(nr*v) ≤ D := by
      rw [div_le_iff₀ hden]
      dsimp [nr] at hD ⊢
      nlinarith
    have hid : (nr+1)/nr*B^2/v = (nr+1)*B^2/(nr*v) := by
      field_simp [ne_of_gt hnr0, ne_of_gt hv]
    rw [hid]
    linarith
  have hx1 : 0 < renewalX1 x u v p q := by
    unfold renewalX1 kernelM1
    positivity
  rw [renewalGap_third_slacks nr x u v p q A B C D
    (ne_of_gt hnr0) (ne_of_gt hu) (ne_of_gt hv)]
  have hslack : 0 ≤ p*q^2*(C-(nr+1)/nr*A^2/u)
      +q^3*(D-(nr+1)/nr*B^2/v) := by positivity
  positivity

/-- Strict part of the two-kernel renewal lemma when both excursion means and the return
probability are positive. -/
theorem renewalGap_pos (n : ℕ) (hn : 4 ≤ n)
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (n:ℝ)/(n-1)*u^2 ≤ A) (hB : (n:ℝ)/(n-1)*v^2 ≤ B)
    (hC : (n+1)*A^2 ≤ (n:ℝ)*u*C)
    (hD : (n+1)*B^2 ≤ (n:ℝ)*v*D) :
    0 < renewalGap n x u v p q A B C D := by
  let nr : ℝ := n
  let l := x+u
  let r := x/l
  let b := p+q*r
  let z := q*v/l
  let da := A/l^2-nr/(nr-1)*(u/l)^2
  let db := q^2*B/l^2-nr/(nr-1)*(q*v/l)^2
  have hnr0 : 0 < nr := by dsimp [nr]; positivity
  have hnr1 : 1 < nr := by dsimp [nr]; exact_mod_cast (show 1 < n by omega)
  have hl : 0 < l := by dsimp [l]; linarith
  have h1r : 0 < 1-r := by
    have hid : 1-r = u/l := by
      dsimp [r, l]
      field_simp [ne_of_gt (show 0 < x+u by linarith)]
      ring
    rw [hid]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hbr : b-r = p*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hrb : r < b := by rw [← sub_pos, hbr]; positivity
  have h1b : 1-b = q*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hb1 : b < 1 := by rw [← sub_pos, h1b]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hda : 0 ≤ da := by
    have hbase : 0 ≤ A-nr/(nr-1)*u^2 := by dsimp [nr]; linarith
    have hid : da=(A-nr/(nr-1)*u^2)/l^2 := by
      dsimp [da]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-nr/(nr-1)*v^2 := by dsimp [nr]; linarith
    have hid : db=q^2/l^2*(B-nr/(nr-1)*v^2) := by
      dsimp [db]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hquad := renewalQuad_pos n hn r b z da db hr0 hrb hb1 hz hda hdb
  have hnorm := renewalGap_normalization nr x u v p q A B (ne_of_gt hnr0)
    (ne_of_gt hnr1) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) hpq
  have hsub : 0 < renewalGapSub nr x u v p q A B := by
    rw [hnorm]
    exact mul_pos (by positivity) hquad
  have hdu : 0 ≤ C-(nr+1)/nr*A^2/u := by
    have hden : 0 < nr*u := mul_pos hnr0 hu
    have hquot : (nr+1)*A^2/(nr*u) ≤ C := by
      rw [div_le_iff₀ hden]
      dsimp [nr] at hC ⊢
      nlinarith
    have hid : (nr+1)/nr*A^2/u=(nr+1)*A^2/(nr*u) := by
      field_simp [ne_of_gt hnr0, ne_of_gt hu]
    rw [hid]
    linarith
  have hdv : 0 ≤ D-(nr+1)/nr*B^2/v := by
    have hden : 0 < nr*v := mul_pos hnr0 hv
    have hquot : (nr+1)*B^2/(nr*v) ≤ D := by
      rw [div_le_iff₀ hden]
      dsimp [nr] at hD ⊢
      nlinarith
    have hid : (nr+1)/nr*B^2/v=(nr+1)*B^2/(nr*v) := by
      field_simp [ne_of_gt hnr0, ne_of_gt hv]
    rw [hid]
    linarith
  rw [renewalGap_third_slacks nr x u v p q A B C D
    (ne_of_gt hnr0) (ne_of_gt hu) (ne_of_gt hv)]
  have hx1 : 0 < renewalX1 x u v p q := by
    unfold renewalX1 kernelM1
    positivity
  have hslack : 0 ≤ p*q^2*(C-(nr+1)/nr*A^2/u)
      +q^3*(D-(nr+1)/nr*B^2/v) := by positivity
  have hterm : 0 ≤ (nr+1)*renewalX1 x u v p q
      *(p*q^2*(C-(nr+1)/nr*A^2/u)+q^3*(D-(nr+1)/nr*B^2/v)) := by positivity
  linarith

/-- Strict renewal inequality when the terminal excursion is the atom at zero. -/
theorem renewalGap_pos_vzero (n : ℕ) (hn : 4 ≤ n)
    (x u p q A C : ℝ) (hx : 0 < x) (hu : 0 < u)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (n:ℝ)/(n-1)*u^2 ≤ A)
    (hC : (n+1)*A^2 ≤ (n:ℝ)*u*C) :
    0 < renewalGap n x u 0 p q A 0 C 0 := by
  let nr : ℝ := n
  let l := x+u
  let r := x/l
  let b := p+q*r
  let da := A/l^2-nr/(nr-1)*(u/l)^2
  have hnr0 : 0 < nr := by dsimp [nr]; positivity
  have hnr1 : 1 < nr := by dsimp [nr]; exact_mod_cast (show 1 < n by omega)
  have hl : 0 < l := by dsimp [l]; linarith
  have h1r : 0 < 1-r := by
    have hid : 1-r=u/l := by
      dsimp [r, l]
      field_simp [ne_of_gt (show 0 < x+u by linarith)]
      ring
    rw [hid]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hbr : b-r=p*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hrb : r < b := by rw [← sub_pos, hbr]; positivity
  have h1b : 1-b=q*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hb1 : b < 1 := by rw [← sub_pos, h1b]; positivity
  have hda : 0 ≤ da := by
    have hbase : 0 ≤ A-nr/(nr-1)*u^2 := by dsimp [nr]; linarith
    have hid : da=(A-nr/(nr-1)*u^2)/l^2 := by
      dsimp [da]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hquad := renewalQuad_alpha_face_pos n hn r b 0 da hr0 hrb hb1 (by norm_num) hda
  have hnorm := renewalGap_normalization_vzero nr x u p q A (ne_of_gt hnr0)
    (ne_of_gt hnr1) (ne_of_gt hu) (ne_of_gt hl) hpq
  have hsub : 0 < renewalGapSubVZero nr x u p q A := by
    rw [hnorm]
    exact mul_pos (by positivity) hquad
  have hdu : 0 ≤ C-(nr+1)/nr*A^2/u := by
    have hden : 0 < nr*u := mul_pos hnr0 hu
    have hquot : (nr+1)*A^2/(nr*u) ≤ C := by
      rw [div_le_iff₀ hden]
      dsimp [nr] at hC ⊢
      nlinarith
    have hid : (nr+1)/nr*A^2/u=(nr+1)*A^2/(nr*u) := by
      field_simp [ne_of_gt hnr0, ne_of_gt hu]
    rw [hid]
    linarith
  rw [renewalGap_vzero_third_slack nr x u p q A C (ne_of_gt hnr0) (ne_of_gt hu)]
  have hx1 : 0 < renewalX1 x u 0 p q := by
    unfold renewalX1 kernelM1
    positivity
  have hterm : 0 ≤ (nr+1)*renewalX1 x u 0 p q*p*q^2
      *(C-(nr+1)/nr*A^2/u) := by positivity
  linarith

/-- Unscaled moments of the renewal sum, recovered from `X_j=q^j E[Z^j]`. -/
noncomputable def renewalM1 (x u v p q : ℝ) : ℝ := renewalX1 x u v p q/q
noncomputable def renewalM2 (x u v p q A B : ℝ) : ℝ := renewalX2 x u v p q A B/q^2
noncomputable def renewalM3 (x u v p q A B C D : ℝ) : ℝ :=
  renewalX3 x u v p q A B C D/q^3

theorem renewalGap_unscale (n x u v p q A B C D : ℝ) (hq : q ≠ 0) :
    gap n (renewalM1 x u v p q) (renewalM2 x u v p q A B)
        (renewalM3 x u v p q A B C D)
      = renewalGap n x u v p q A B C D/q^4 := by
  unfold gap renewalM1 renewalM2 renewalM3 renewalGap
  field_simp [hq]

/-- Moment-form statement of the nondegenerate two-kernel renewal lemma. -/
theorem renewal_moment_inequality (n : ℕ) (hn : 4 ≤ n)
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (n:ℝ)/(n-1)*u^2 ≤ A) (hB : (n:ℝ)/(n-1)*v^2 ≤ B)
    (hC : (n+1)*A^2 ≤ (n:ℝ)*u*C)
    (hD : (n+1)*B^2 ≤ (n:ℝ)*v*D) :
    (n+2)*(renewalM2 x u v p q A B)^2
      ≤ (n+1)*renewalM1 x u v p q*renewalM3 x u v p q A B C D := by
  have hgap := renewalGap_nonneg n hn x u v p q A B C D hx hu hv hp hq hpq
    hA hB hC hD
  have huq := renewalGap_unscale n x u v p q A B C D (ne_of_gt hq)
  have hq4 : 0 < q^4 := by positivity
  unfold gap at huq
  have hscaled := div_nonneg hgap (le_of_lt hq4)
  linarith

theorem renewal_moment_strict (n : ℕ) (hn : 4 ≤ n)
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (n:ℝ)/(n-1)*u^2 ≤ A) (hB : (n:ℝ)/(n-1)*v^2 ≤ B)
    (hC : (n+1)*A^2 ≤ (n:ℝ)*u*C)
    (hD : (n+1)*B^2 ≤ (n:ℝ)*v*D) :
    (n+2)*(renewalM2 x u v p q A B)^2
      < (n+1)*renewalM1 x u v p q*renewalM3 x u v p q A B C D := by
  have hgap := renewalGap_pos n hn x u v p q A B C D hx hu hv hp hq hpq
    hA hB hC hD
  have huq := renewalGap_unscale n x u v p q A B C D (ne_of_gt hq)
  have hscaled : 0 < renewalGap (n:ℝ) x u v p q A B C D/q^4 := by positivity
  unfold gap at huq
  linarith

/-- On the no-return face `p=0` the translated quadratic is one-dimensional; the unused
`A` displacement may be arbitrary. -/
theorem renewalQuad_nonneg_pzero (n : ℕ) (hn : 4 ≤ n) (r z da db : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hz : 0 < z) (hdb : 0 ≤ db) :
    0 ≤ renewalQuad n r r z da db := by
  let nr : ℝ := n
  have hnr0 : 0 < nr := by dsimp [nr]; positivity
  have hnr1 : 1 < nr := by dsimp [nr]; exact_mod_cast (show 1 < n by omega)
  have hcorner : 0 ≤ Phi nr r r z :=
    corner_nonneg n hn r r z (le_of_lt hr0) le_rfl (le_of_lt hr1) (le_of_lt hz)
  have hq0 : 0 ≤ Phi nr r r z/(nr-1)^2 := by positivity
  have hhbb : 0 < hBetaBeta nr r z := by unfold hBetaBeta; positivity
  have hdisc : gBeta nr r r z < 0 →
      0 ≤ 2*hBetaBeta nr r z*(Phi nr r r z/(nr-1)^2)-(gBeta nr r r z)^2 := by
    intro hg
    have hS : SBeta nr r r z ≤ 0 := by
      unfold gBeta at hg
      rw [div_neg_iff] at hg
      rcases hg with hg | hg
      · linarith
      · exact le_of_lt hg.1
    have hK := kBeta_nonneg n hn r r z (le_of_lt hr0) le_rfl (le_of_lt hr1)
      (le_of_lt hz) hS
    rw [beta_face_discriminant nr r r z (ne_of_gt hnr0) (ne_of_gt hnr1)
      (ne_of_gt hz)]
    positivity
  have hface := quad1_nonneg (Phi nr r r z/(nr-1)^2) (gBeta nr r r z)
    (hBetaBeta nr r z) db hq0 hhbb hdb hdisc
  unfold renewalQuad quad2
  unfold gAlpha hAlphaAlpha hAlphaBeta
  norm_num
  simpa [nr] using hface

/-- Sharpness on the no-return face: the normalized gap vanishes only at the lower
second-moment endpoint and at the Erlang mean matching condition. -/
theorem renewalQuad_pzero_eq_zero_iff (n : ℕ) (hn : 4 ≤ n) (r z da db : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hz : 0 < z) (hdb : 0 ≤ db) :
    renewalQuad n r r z da db = 0 ↔ db = 0 ∧ z=(n-1)*r := by
  let nr : ℝ := n
  have hnr4 : 4 ≤ nr := by dsimp [nr]; exact_mod_cast hn
  have hnr0 : 0 < nr := by linarith
  have hnr1 : 1 < nr := by linarith
  have hq0 : 0 ≤ Phi nr r r z/(nr-1)^2 := by
    have := corner_nonneg n hn r r z (le_of_lt hr0) le_rfl (le_of_lt hr1) (le_of_lt hz)
    positivity
  have hh : 0 < hBetaBeta nr r z := by unfold hBetaBeta; positivity
  have hreduce : renewalQuad nr r r z da db
      = Phi nr r r z/(nr-1)^2+gBeta nr r r z*db+hBetaBeta nr r z*db^2/2 := by
    unfold renewalQuad quad2 gAlpha hAlphaAlpha hAlphaBeta
    ring
  constructor
  · intro hzero
    have hdb0 : db = 0 := by
      by_contra hne
      have hdbpos : 0 < db := lt_of_le_of_ne hdb (Ne.symm hne)
      have hstrict : 0 < Phi nr r r z/(nr-1)^2+gBeta nr r r z*db
          +hBetaBeta nr r z*db^2/2 := by
        rcases le_or_gt 0 (gBeta nr r r z) with hg | hg
        · have hlin : 0 ≤ gBeta nr r r z*db := mul_nonneg hg hdb
          have hquad : 0 < hBetaBeta nr r z*db^2/2 := by positivity
          linarith
        · let y := z/r
          have hy : 0 ≤ y := by dsimp [y]; positivity
          have hzy : z = r*y := by dsimp [y]; field_simp
          have hS : SBeta nr r r z < 0 := by
            unfold gBeta at hg
            rw [div_neg_iff] at hg
            rcases hg with hg | hg
            · linarith
            · exact hg.1
          have hf : FBeta nr y < 0 := by
            have hid := sBeta_at_b_scaled nr r y
            rw [← hzy] at hid
            rw [hid] at hS
            change r^2*FBeta nr y < 0 at hS
            have hr2 : 0 < r^2 := sq_pos_of_pos hr0
            nlinarith
          have hthreshold := fBeta_threshold_strict nr y hnr4 hy hf
          have hfac : 0 < 8*(nr-1)*r-(nr+8)*z := by
            rw [hzy]
            nlinarith [mul_pos hr0 (sub_pos.mpr hthreshold)]
          have hK : 0 < KBeta nr r r z := by
            rw [kBeta_at_b]
            have hnfac : 0 < (nr^2-1)^2 := by
              have : 0 < nr^2-1 := by
                nlinarith [mul_pos (sub_pos.mpr hnr1) (show 0 < nr+1 by linarith)]
              positivity
            exact mul_pos (mul_pos (mul_pos hnfac hfac) (sq_pos_of_pos hr0))
              (sq_pos_of_pos (by linarith))
          have hdiscEq := beta_face_discriminant nr r r z (ne_of_gt hnr0)
            (ne_of_gt hnr1) (ne_of_gt hz)
          have hdisc : 0 < 2*hBetaBeta nr r z*(Phi nr r r z/(nr-1)^2)
              -(gBeta nr r r z)^2 := by
            rw [hdiscEq]
            positivity
          have hid : Phi nr r r z/(nr-1)^2+gBeta nr r r z*db
                +hBetaBeta nr r z*db^2/2
              = (2*hBetaBeta nr r z*(Phi nr r r z/(nr-1)^2)
                    -(gBeta nr r r z)^2)/(2*hBetaBeta nr r z)
                +hBetaBeta nr r z/2*(db+gBeta nr r r z/hBetaBeta nr r z)^2 := by
            field_simp [ne_of_gt hh]
            ring
          rw [hid]
          have hfirst : 0 < (2*hBetaBeta nr r z*(Phi nr r r z/(nr-1)^2)
                    -(gBeta nr r r z)^2)/(2*hBetaBeta nr r z) := by positivity
          have hsecond : 0 ≤ hBetaBeta nr r z/2
              *(db+gBeta nr r r z/hBetaBeta nr r z)^2 := by positivity
          linarith
      rw [hreduce] at hzero
      linarith
    have hphi0 : Phi nr r r z = 0 := by
      change renewalQuad nr r r z da db = 0 at hzero
      rw [hdb0] at hzero hreduce
      norm_num at hreduce
      rw [hreduce] at hzero
      have hden : 0 < (nr-1)^2 := sq_pos_of_pos (by linarith)
      exact (div_eq_zero_iff).mp hzero |>.resolve_right (ne_of_gt hden)
    have hfactor := phi_at_b nr r z
    rw [hfactor] at hphi0
    have hpref : 0 < 2*(nr-1)*r^2+4*nr*r*z+nr*z^2 := by positivity
    have hsquare : (z-(nr-1)*r)^2 = 0 := (mul_eq_zero.mp hphi0).resolve_left (ne_of_gt hpref)
    have hzrel : z=(nr-1)*r := by nlinarith [sq_nonneg (z-(nr-1)*r)]
    exact ⟨hdb0, by simpa [nr] using hzrel⟩
  · rintro ⟨rfl, hzrel⟩
    rw [hreduce]
    norm_num
    rw [phi_at_b]
    simp [nr, hzrel]

/-- The renewal inequality on the no-return face, including arbitrary admissible second and
third moments of the terminal excursion. -/
theorem no_return_moment_inequality (n : ℕ) (hn : 4 ≤ n)
    (x v B D : ℝ) (hx : 0 < x) (hv : 0 < v)
    (hB : (n:ℝ)/(n-1)*v^2 ≤ B)
    (hD : (n+1)*B^2 ≤ (n:ℝ)*v*D) :
    (n+2)*(kernelM2 x v B)^2 ≤ (n+1)*kernelM1 x v*kernelM3 x v B D := by
  let nr : ℝ := n
  let u := x
  let A := nr/(nr-1)*u^2
  let l := x+u
  let r := x/l
  let z := v/l
  let db := B/l^2-nr/(nr-1)*z^2
  have hnr0 : 0 < nr := by dsimp [nr]; positivity
  have hnr1 : 1 < nr := by dsimp [nr]; exact_mod_cast (show 1 < n by omega)
  have hu : 0 < u := by simpa [u]
  have hl : 0 < l := by dsimp [l, u]; linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r, l, u]
    rw [div_lt_one (by linarith)]
    linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-nr/(nr-1)*v^2 := by dsimp [nr]; linarith
    have hid : db = (B-nr/(nr-1)*v^2)/l^2 := by
      dsimp [db, z]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  let da := A/l^2-nr/(nr-1)*(u/l)^2
  have hquad := renewalQuad_nonneg_pzero n hn r z da db hr0 hr1 hz hdb
  have hnorm := renewalGap_normalization nr x u v 0 1 A B (ne_of_gt hnr0)
    (ne_of_gt hnr1) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) (by norm_num)
  have hsub : 0 ≤ renewalGapSub nr x u v 0 1 A B := by
    rw [hnorm]
    norm_num at hnorm ⊢
    exact mul_nonneg (by positivity) hquad
  have hdv : 0 ≤ D-(nr+1)/nr*B^2/v := by
    have hden : 0 < nr*v := mul_pos hnr0 hv
    have hquot : (nr+1)*B^2/(nr*v) ≤ D := by
      rw [div_le_iff₀ hden]
      dsimp [nr] at hD ⊢
      nlinarith
    have hid : (nr+1)/nr*B^2/v = (nr+1)*B^2/(nr*v) := by
      field_simp [ne_of_gt hnr0, ne_of_gt hv]
    rw [hid]
    linarith
  have hgapid := renewalGap_third_slacks nr x u v 0 1 A B 0 D
    (ne_of_gt hnr0) (ne_of_gt hu) (ne_of_gt hv)
  norm_num at hgapid
  have hgap : 0 ≤ renewalGap nr x u v 0 1 A B 0 D := by
    rw [hgapid]
    unfold renewalX1 kernelM1
    positivity
  unfold renewalGap renewalX1 renewalX2 renewalX3 at hgap
  norm_num [kernelM1, kernelM2, kernelM3] at hgap
  exact hgap

theorem no_return_atom_strict (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x) :
    (n+2)*(kernelM2 x 0 0)^2
      < (n+1)*kernelM1 x 0*kernelM3 x 0 0 0 := by
  unfold kernelM1 kernelM2 kernelM3
  norm_num
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn
  nlinarith [sq_pos_of_pos (sq_pos_of_pos hx)]

/-- Complete equality characterization for the no-return renewal face. -/
theorem no_return_equality_iff (n : ℕ) (hn : 4 ≤ n)
    (x v B D : ℝ) (hx : 0 < x) (hv : 0 < v)
    (hB : (n:ℝ)/(n-1)*v^2 ≤ B)
    (hD : (n+1)*B^2 ≤ (n:ℝ)*v*D) :
    (n+1)*kernelM1 x v*kernelM3 x v B D-(n+2)*(kernelM2 x v B)^2 = 0
      ↔ B=(n:ℝ)/(n-1)*v^2 ∧
        D=(n+1)/(n:ℝ)*B^2/v ∧ v=((n:ℝ)-1)*x := by
  let nr : ℝ := n
  let u := x
  let A := nr/(nr-1)*u^2
  let l := x+u
  let r := x/l
  let z := v/l
  let db := B/l^2-nr/(nr-1)*z^2
  let da := A/l^2-nr/(nr-1)*(u/l)^2
  have hnr0 : 0 < nr := by dsimp [nr]; positivity
  have hnr1 : 1 < nr := by dsimp [nr]; exact_mod_cast (show 1 < n by omega)
  have hu : 0 < u := by simpa [u]
  have hl : 0 < l := by dsimp [l, u]; linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r, l, u]
    rw [div_lt_one (by linarith)]
    linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-nr/(nr-1)*v^2 := by dsimp [nr]; linarith
    have hid : db = (B-nr/(nr-1)*v^2)/l^2 := by
      dsimp [db, z]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hdu : 0 ≤ D-(nr+1)/nr*B^2/v := by
    have hden : 0 < nr*v := mul_pos hnr0 hv
    have hquot : (nr+1)*B^2/(nr*v) ≤ D := by
      rw [div_le_iff₀ hden]
      dsimp [nr] at hD ⊢
      nlinarith
    have hid : (nr+1)/nr*B^2/v = (nr+1)*B^2/(nr*v) := by
      field_simp [ne_of_gt hnr0, ne_of_gt hv]
    rw [hid]
    linarith
  have hquadnon := renewalQuad_nonneg_pzero n hn r z da db hr0 hr1 hz hdb
  have hnorm := renewalGap_normalization nr x u v 0 1 A B (ne_of_gt hnr0)
    (ne_of_gt hnr1) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) (by norm_num)
  have hnorm' : renewalGapSub nr x u v 0 1 A B
      = l^4*renewalQuad nr r r z da db := by
    simpa [l, r, z, da, db] using hnorm
  have hsub : 0 ≤ renewalGapSub nr x u v 0 1 A B := by
    rw [hnorm']
    exact mul_nonneg (by positivity) hquadnon
  have hgapid := renewalGap_third_slacks nr x u v 0 1 A B 0 D
    (ne_of_gt hnr0) (ne_of_gt hu) (ne_of_gt hv)
  norm_num [renewalX1, kernelM1] at hgapid
  have hxv : 0 < (nr+1)*(x+v) := by positivity
  constructor
  · intro heq
    have hrenew : renewalGap nr x u v 0 1 A B 0 D = 0 := by
      unfold renewalGap renewalX1 renewalX2 renewalX3
      norm_num [kernelM1, kernelM2, kernelM3]
      exact heq
    have hsumzero : renewalGapSub nr x u v 0 1 A B
        +(nr+1)*(x+v)*(D-(nr+1)*B^2/(nr*v)) = 0 := by
      rw [hgapid] at hrenew
      convert hrenew using 1
      all_goals ring
    have hdu' : 0 ≤ D-(nr+1)*B^2/(nr*v) := by
      have hid : (nr+1)/nr*B^2/v = (nr+1)*B^2/(nr*v) := by
        field_simp [ne_of_gt hnr0, ne_of_gt hv]
      rw [← hid]
      exact hdu
    have hthirdterm : 0 ≤ (nr+1)*(x+v)*(D-(nr+1)*B^2/(nr*v)) :=
      mul_nonneg (le_of_lt hxv) hdu'
    have hsubzero : renewalGapSub nr x u v 0 1 A B = 0 := by linarith
    have hthirdzero : D-(nr+1)*B^2/(nr*v) = 0 := by
      have hprod : (nr+1)*(x+v)*(D-(nr+1)*B^2/(nr*v)) = 0 := by linarith
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hxv)
    have hquadzero : renewalQuad nr r r z da db = 0 := by
      have hl4 : 0 < l^4 := by positivity
      rw [hnorm'] at hsubzero
      exact (mul_eq_zero.mp hsubzero).resolve_left (ne_of_gt hl4)
    have hsharp := (renewalQuad_pzero_eq_zero_iff n hn r z da db hr0 hr1 hz hdb).mp hquadzero
    have hBeq : B=nr/(nr-1)*v^2 := by
      have hid : db = (B-nr/(nr-1)*v^2)/l^2 := by
        dsimp [db, z]
        field_simp [ne_of_gt hl]
      rw [hsharp.1] at hid
      have hl2 : l^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hl)
      field_simp [hl2] at hid
      have halg : nr*v^2/(nr-1) = nr/(nr-1)*v^2 := by ring
      linarith
    have hveq : v=(nr-1)*x := by
      have hzrel := hsharp.2
      dsimp [z, r, l, u] at hzrel
      field_simp [show x+x ≠ 0 by linarith] at hzrel
      linarith
    have hDeq : D=(nr+1)/nr*B^2/v := by
      have hid : (nr+1)*B^2/(nr*v) = (nr+1)/nr*B^2/v := by
        field_simp [ne_of_gt hnr0, ne_of_gt hv]
      linarith
    exact ⟨by simpa [nr] using hBeq, by simpa [nr] using hDeq,
      by simpa [nr] using hveq⟩
  · rintro ⟨hBeq, hDeq, hveq⟩
    rw [hDeq, hBeq, hveq]
    unfold kernelM1 kernelM2 kernelM3
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    have hn1 : (n:ℝ)-1 ≠ 0 := by nlinarith
    field_simp [hn0, hn1]
    ring

/-- Equality statement for the complete two-kernel renewal step.  In particular, equality
forces the return probability to vanish. -/
theorem renewal_equality_iff (n : ℕ) (hn : 4 ≤ n)
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p+q=1)
    (hreturn : 0 < p → 0 < u)
    (hvzero : v=0 → B=0 ∧ D=0)
    (hA : (n:ℝ)/(n-1)*u^2 ≤ A) (hB : (n:ℝ)/(n-1)*v^2 ≤ B)
    (hC : (n+1)*A^2 ≤ (n:ℝ)*u*C)
    (hD : (n+1)*B^2 ≤ (n:ℝ)*v*D) :
    gap n (renewalM1 x u v p q) (renewalM2 x u v p q A B)
        (renewalM3 x u v p q A B C D) = 0
      ↔ p=0 ∧ B=(n:ℝ)/(n-1)*v^2 ∧
        D=(n+1)/(n:ℝ)*B^2/v ∧ v=((n:ℝ)-1)*x := by
  constructor
  · intro heq
    have hpzero : p=0 := by
      by_contra hne
      have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hne)
      have hupos := hreturn hppos
      rcases eq_or_lt_of_le hv with hv0 | hvpos
      · have hv0' : v=0 := hv0.symm
        have hz := hvzero hv0'
        have hraw := renewalGap_pos_vzero n hn x u p q A C hx hupos hppos hq hpq hA hC
        have hun := renewalGap_unscale n x u 0 p q A 0 C 0 (ne_of_gt hq)
        have hscaled : 0 < renewalGap (n:ℝ) x u 0 p q A 0 C 0/q^4 :=
          div_pos hraw (pow_pos hq 4)
        rw [hv0', hz.1, hz.2] at heq
        linarith
      · have hstrict := renewal_moment_strict n hn x u v p q A B C D hx hupos hvpos
          hppos hq hpq hA hB hC hD
        unfold gap at heq
        linarith
    have hqone : q=1 := by linarith
    rcases eq_or_lt_of_le hv with hv0 | hvpos
    · have hv0' : v=0 := hv0.symm
      have hz := hvzero hv0'
      have hstrict := no_return_atom_strict n (by omega) x hx
      rw [hpzero, hqone, hv0', hz.1, hz.2] at heq
      unfold gap at heq
      simp [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
        kernelM1, kernelM2, kernelM3] at heq
      unfold kernelM1 kernelM2 kernelM3 at hstrict
      norm_num at hstrict
      nlinarith
    · have hiff := no_return_equality_iff n hn x v B D hx hvpos hB hD
      have hkernel : (n+1)*kernelM1 x v*kernelM3 x v B D
          -(n+2)*(kernelM2 x v B)^2=0 := by
        rw [hpzero, hqone] at heq
        unfold gap at heq
        simpa [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
          kernelM1, kernelM2, kernelM3] using heq
      exact ⟨hpzero, (hiff.mp hkernel).1, (hiff.mp hkernel).2.1, (hiff.mp hkernel).2.2⟩
  · rintro ⟨hpzero, hBeq, hDeq, hveq⟩
    have hqone : q=1 := by linarith
    have hvpos : 0 < v := by
      rw [hveq]
      have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      positivity
    have hiff := no_return_equality_iff n hn x v B D hx hvpos hB hD
    have hkernel := hiff.mpr ⟨hBeq, hDeq, hveq⟩
    rw [hpzero, hqone]
    unfold gap
    simpa [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
      kernelM1, kernelM2, kernelM3] using hkernel

/-! ## The `p=0` equality face -/

/-- On the no-return face, the lower-corner gap is a positive factor times
`(v-(n-1)x)²`. -/
theorem no_return_corner_factor (n x v : ℝ) (hn : n ≠ 1) :
    (n+1)*(x+v)
        *(6*x^3 + 6*x^2*v + 3*x*(n*v^2/(n-1)) + n*(n+1)*v^3/(n-1)^2)
      - (n+2)*(2*x^2 + 2*x*v + n*v^2/(n-1))^2
      = ((2*(n-1)*x^2 + 4*n*x*v + n*v^2) / (n-1)^2)
          * (v-(n-1)*x)^2 := by
  have hn' : n - 1 ≠ 0 := sub_ne_zero.mpr hn
  field_simp [hn']
  ring

/-- The third-moment slack enters the no-return gap with a strictly positive coefficient. -/
theorem no_return_third_slack (n x v B δ : ℝ) :
    (n+1)*(x+v)*(6*x^3 + 6*x^2*v + 3*x*B + ((n+1)/n)*B^2/v + δ)
        - (n+2)*(2*x^2 + 2*x*v + B)^2
      = ((n+1)*(x+v)*(6*x^3 + 6*x^2*v + 3*x*B + ((n+1)/n)*B^2/v)
        - (n+2)*(2*x^2 + 2*x*v + B)^2) + (n+1)*(x+v)*δ := by
  ring

/-! ## Abstract assembly of the all-orders induction -/

/-- The raw-moment `k=2` assertion at stage count `s`. -/
def StageBound (s : ℕ) (m₁ m₂ m₃ : ℝ) : Prop :=
  (s+2)*m₂^2 ≤ (s+1)*m₁*m₃

/-- A bound proved with a smaller stage count remains true with any larger stage count. -/
theorem stageBound_mono {s N : ℕ} {m₁ m₂ m₃ : ℝ}
    (hs : 1 ≤ s) (hsN : s ≤ N) (_hm₁ : 0 ≤ m₁) (_hm₂ : 0 ≤ m₂)
    (_hm₃ : 0 ≤ m₃) (h : StageBound s m₁ m₂ m₃) :
    StageBound N m₁ m₂ m₃ := by
  let d : ℝ := ((N-s : ℕ) : ℝ)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs0 : 0 < (s: ℝ)+1 := by positivity
  have hab : m₂^2 ≤ m₁*m₃ := by
    unfold StageBound at h
    have hsq : 0 ≤ m₂^2 := sq_nonneg _
    nlinarith
  have hprod : 0 ≤ d*(m₁*m₃-m₂^2) := mul_nonneg hd (sub_nonneg.mpr hab)
  have hcast : (N:ℝ) = s+d := by
    dsimp [d]
    rw [Nat.cast_sub hsN]
    ring
  unfold StageBound at h ⊢
  rw [hcast]
  nlinarith

/-- The data supplied by the strong-Markov state-return decomposition of a deterministic-start
order-`n` phase-type law.  The two Aldous--Shepp inequalities are included as fields because they
are already proved independently in `SSPLean.AldousSheppFinal`. -/
structure RenewalCertificate (Law : ℕ → Type*)
    (mom₁ mom₂ mom₃ : ∀ s, Law s → ℝ) (n : ℕ) (X : Law n) where
  su : ℕ
  sv : ℕ
  su_pos : 1 ≤ su
  sv_pos : 1 ≤ sv
  su_lt : su < n
  sv_lt : sv < n
  U : Law su
  V : Law sv
  x : ℝ
  p : ℝ
  q : ℝ
  x_pos : 0 < x
  p_nonneg : 0 ≤ p
  q_pos : 0 < q
  prob_sum : p+q=1
  return_mean_pos : 0 < p → 0 < mom₁ su U
  terminal_zero : mom₁ sv V = 0 → mom₂ sv V = 0 ∧ mom₃ sv V = 0
  as_U : (n:ℝ)/(n-1)*(mom₁ su U)^2 ≤ mom₂ su U
  as_V : (n:ℝ)/(n-1)*(mom₁ sv V)^2 ≤ mom₂ sv V
  moment1 : mom₁ n X = renewalM1 x (mom₁ su U) (mom₁ sv V) p q
  moment2 : mom₂ n X = renewalM2 x (mom₁ su U) (mom₁ sv V) p q
    (mom₂ su U) (mom₂ sv V)
  moment3 : mom₃ n X = renewalM3 x (mom₁ su U) (mom₁ sv V) p q
    (mom₂ su U) (mom₂ sv V) (mom₃ su U) (mom₃ sv V)

/-- The complete logical induction after the base cases and state-return representation have
been supplied.  Thus no algebraic or induction step remains outside Lean. -/
theorem all_stages_of_renewal
    (Law : ℕ → Type*) (mom₁ mom₂ mom₃ : ∀ s, Law s → ℝ)
    (hm₁ : ∀ s (X : Law s), 0 ≤ mom₁ s X)
    (hm₂ : ∀ s (X : Law s), 0 ≤ mom₂ s X)
    (hm₃ : ∀ s (X : Law s), 0 ≤ mom₃ s X)
    (hbase : ∀ s, 1 ≤ s → s ≤ 3 → ∀ X : Law s,
      StageBound s (mom₁ s X) (mom₂ s X) (mom₃ s X))
    (hrenew : ∀ n, 4 ≤ n → ∀ X : Law n,
      RenewalCertificate Law mom₁ mom₂ mom₃ n X) :
    ∀ n, 1 ≤ n → ∀ X : Law n,
      StageBound n (mom₁ n X) (mom₂ n X) (mom₃ n X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnpos X
      by_cases hn3 : n ≤ 3
      · exact hbase n hnpos hn3 X
      · have hn4 : 4 ≤ n := by omega
        let c := hrenew n hn4 X
        have hU0 := ih c.su c.su_lt c.su_pos c.U
        have hV0 := ih c.sv c.sv_lt c.sv_pos c.V
        have hsuN : c.su ≤ n-1 := Nat.le_sub_one_of_lt c.su_lt
        have hsvN : c.sv ≤ n-1 := Nat.le_sub_one_of_lt c.sv_lt
        have hU := stageBound_mono c.su_pos hsuN (hm₁ c.su c.U) (hm₂ c.su c.U)
          (hm₃ c.su c.U) hU0
        have hV := stageBound_mono c.sv_pos hsvN (hm₁ c.sv c.V) (hm₂ c.sv c.V)
          (hm₃ c.sv c.V) hV0
        have hUc : (n+1)*(mom₂ c.su c.U)^2
            ≤ (n:ℝ)*(mom₁ c.su c.U)*(mom₃ c.su c.U) := by
          unfold StageBound at hU
          have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
          rw [hncast] at hU
          norm_num at hU
          nlinarith
        have hVc : (n+1)*(mom₂ c.sv c.V)^2
            ≤ (n:ℝ)*(mom₁ c.sv c.V)*(mom₃ c.sv c.V) := by
          unfold StageBound at hV
          have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
          rw [hncast] at hV
          norm_num at hV
          nlinarith
        rcases eq_or_lt_of_le c.p_nonneg with hp0 | hp0
        · have hq1 : c.q=1 := by linarith [c.prob_sum]
          rcases eq_or_lt_of_le (hm₁ c.sv c.V) with hv0 | hv0
          · have hv23 := c.terminal_zero hv0.symm
            have hstrict := no_return_atom_strict n (by omega) c.x c.x_pos
            unfold StageBound
            rw [c.moment1, c.moment2, c.moment3, ← hp0, hq1, ← hv0, hv23.1, hv23.2]
            simpa [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
              kernelM1, kernelM2, kernelM3] using le_of_lt hstrict
          · have hnr := no_return_moment_inequality n hn4 c.x (mom₁ c.sv c.V)
              (mom₂ c.sv c.V) (mom₃ c.sv c.V) c.x_pos hv0 c.as_V hVc
            unfold StageBound
            rw [c.moment1, c.moment2, c.moment3, ← hp0, hq1]
            simpa [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
              kernelM1, kernelM2, kernelM3] using hnr
        · have hu0 := c.return_mean_pos hp0
          rcases eq_or_lt_of_le (hm₁ c.sv c.V) with hv0 | hv0
          · have hv23 := c.terminal_zero hv0.symm
            have hstrict := renewalGap_pos_vzero n hn4 c.x (mom₁ c.su c.U) c.p c.q
              (mom₂ c.su c.U) (mom₃ c.su c.U) c.x_pos hu0 hp0 c.q_pos
              c.prob_sum c.as_U hUc
            unfold StageBound
            rw [c.moment1, c.moment2, c.moment3, ← hv0, hv23.1, hv23.2]
            have hunscale := renewalGap_unscale n c.x (mom₁ c.su c.U) 0 c.p c.q
              (mom₂ c.su c.U) 0 (mom₃ c.su c.U) 0 (ne_of_gt c.q_pos)
            unfold gap at hunscale
            have : 0 < renewalGap (n:ℝ) c.x (mom₁ c.su c.U) 0 c.p c.q
                (mom₂ c.su c.U) 0 (mom₃ c.su c.U) 0/c.q^4 :=
              div_pos hstrict (pow_pos c.q_pos 4)
            linarith
          · have hmain := renewal_moment_inequality n hn4 c.x (mom₁ c.su c.U)
              (mom₁ c.sv c.V) c.p c.q (mom₂ c.su c.U) (mom₂ c.sv c.V)
              (mom₃ c.su c.U) (mom₃ c.sv c.V) c.x_pos hu0 hv0 hp0 c.q_pos
              c.prob_sum c.as_U c.as_V hUc hVc
            unfold StageBound
            rwa [c.moment1, c.moment2, c.moment3]

/-! ## Equality after mixing deterministic starting states -/

theorem weighted_scale_variance_identity (t : Finset ι) (w θ : ι → ℝ) :
    2*((∑ i ∈ t, w i*θ i)*(∑ i ∈ t, w i*(θ i)^3)
        -(∑ i ∈ t, w i*(θ i)^2)^2)
      = ∑ i ∈ t, ∑ j ∈ t, w i*w j*θ i*θ j*(θ i-θ j)^2 := by
  let A := ∑ i ∈ t, ∑ j ∈ t, w i*w j*(θ i)^3*θ j
  let B := ∑ i ∈ t, ∑ j ∈ t, w i*w j*θ i*(θ j)^3
  let C := ∑ i ∈ t, ∑ j ∈ t, w i*w j*(θ i)^2*(θ j)^2
  have hswap : A=B := by
    dsimp [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hprod13 : (∑ i ∈ t, w i*θ i)*(∑ j ∈ t, w j*(θ j)^3)=B := by
    dsimp [B]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hprod22 : (∑ i ∈ t, w i*(θ i)^2)^2=C := by
    dsimp [C]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hrhs : (∑ i ∈ t, ∑ j ∈ t, w i*w j*θ i*θ j*(θ i-θ j)^2)
      = A+B-2*C := by
    dsimp [A, B, C]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hprod13, hprod22, hrhs, hswap]
  ring

theorem weighted_scale_variance_nonneg (t : Finset ι) (w θ : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hθ : ∀ i ∈ t, 0 ≤ θ i) :
    0 ≤ (∑ i ∈ t, w i*θ i)*(∑ i ∈ t, w i*(θ i)^3)
        -(∑ i ∈ t, w i*(θ i)^2)^2 := by
  have hid := weighted_scale_variance_identity t w θ
  have hrhs : 0 ≤ ∑ i ∈ t, ∑ j ∈ t, w i*w j*θ i*θ j*(θ i-θ j)^2 := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hθ i hi)) (hθ j hj))
      (sq_nonneg _)
  nlinarith

/-- Equality in the final mixture forces every pair of positively weighted Erlang components
to have the same scale. -/
theorem weighted_scale_variance_eq_zero_iff (t : Finset ι) (w θ : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hθ : ∀ i ∈ t, 0 < θ i) :
    (∑ i ∈ t, w i*θ i)*(∑ i ∈ t, w i*(θ i)^3)
          -(∑ i ∈ t, w i*(θ i)^2)^2 = 0
      ↔ ∀ i ∈ t, ∀ j ∈ t, 0 < w i → 0 < w j → θ i=θ j := by
  have hterm : ∀ i ∈ t, ∀ j ∈ t, 0 ≤ w i*w j*θ i*θ j*(θ i-θ j)^2 := by
    intro i hi j hj
    have := hw i hi
    have := hw j hj
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (le_of_lt (hθ i hi)))
        (le_of_lt (hθ j hj))) (sq_nonneg _)
  constructor
  · intro hzero i hi j hj hwi hwj
    have hid := weighted_scale_variance_identity t w θ
    rw [hzero] at hid
    norm_num at hid
    have halli := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi =>
      Finset.sum_nonneg (fun j hj => hterm i hi j hj))).mp hid.symm i hi
    have hallj := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hterm i hi j hj)).mp halli j hj
    have hpref : 0 < w i*w j*θ i*θ j := by
      exact mul_pos (mul_pos (mul_pos hwi hwj) (hθ i hi)) (hθ j hj)
    have hsquare : (θ i-θ j)^2=0 :=
      (mul_eq_zero.mp hallj).resolve_left (ne_of_gt hpref)
    nlinarith [sq_nonneg (θ i-θ j)]
  · intro hpairs
    have hrhs0 : (∑ i ∈ t, ∑ j ∈ t, w i*w j*θ i*θ j*(θ i-θ j)^2)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rcases eq_or_lt_of_le (hw i hi) with hwi | hwi
      · rw [← hwi]
        ring
      rcases eq_or_lt_of_le (hw j hj) with hwj | hwj
      · rw [← hwj]
        ring
      rw [hpairs i hi j hj hwi hwj]
      ring
    have hid := weighted_scale_variance_identity t w θ
    rw [hrhs0] at hid
    linarith

theorem erlang_components_gap (s : ℕ) (t : Finset ι) (w θ : ι → ℝ) :
    gap s
      (∑ i ∈ t, w i*s*θ i)
      (∑ i ∈ t, w i*s*(s+1)*(θ i)^2)
      (∑ i ∈ t, w i*s*(s+1)*(s+2)*(θ i)^3)
      = (s:ℝ)^2*(s+1)^2*(s+2)
          *((∑ i ∈ t, w i*θ i)*(∑ i ∈ t, w i*(θ i)^3)
            -(∑ i ∈ t, w i*(θ i)^2)^2) := by
  have e1 : (∑ i ∈ t, w i*s*θ i)=(s:ℝ)*(∑ i ∈ t, w i*θ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have e2 : (∑ i ∈ t, w i*s*(s+1)*(θ i)^2)
      =(s:ℝ)*(s+1)*(∑ i ∈ t, w i*(θ i)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have e3 : (∑ i ∈ t, w i*s*(s+1)*(s+2)*(θ i)^3)
      =(s:ℝ)*(s+1)*(s+2)*(∑ i ∈ t, w i*(θ i)^3) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold gap
  rw [e1, e2, e3]
  ring

theorem erlang_components_equality_scales (s : ℕ) (hs : 1 ≤ s)
    (t : Finset ι) (w θ : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hθ : ∀ i ∈ t, 0 < θ i)
    (heq : gap s
      (∑ i ∈ t, w i*s*θ i)
      (∑ i ∈ t, w i*s*(s+1)*(θ i)^2)
      (∑ i ∈ t, w i*s*(s+1)*(s+2)*(θ i)^3)=0) :
    ∀ i ∈ t, ∀ j ∈ t, 0 < w i → 0 < w j → θ i=θ j := by
  rw [erlang_components_gap] at heq
  have hfac : 0 < (s:ℝ)^2*(s+1)^2*(s+2) := by positivity
  have hvar : (∑ i ∈ t, w i*θ i)*(∑ i ∈ t, w i*(θ i)^3)
      -(∑ i ∈ t, w i*(θ i)^2)^2=0 :=
    (mul_eq_zero.mp heq).resolve_left (ne_of_gt hfac)
  exact (weighted_scale_variance_eq_zero_iff t w θ hw hθ).mp hvar

end SSP.K2AllStages
