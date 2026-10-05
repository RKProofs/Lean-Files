import SSPLean.K3S4Renewal

/-!
# The fourth-moment resolvent renewal identity

This file extends the state-return resolvent recursion of `SSPLean.K2ConcreteInitial` by one
order.  That file proves `transient_first/second/third_resolvent_renewal`, which express

`τ · (Nᵏ𝟙)ᵢ`   (τ = terminal probability, N = (1-Q)⁻¹)

in terms of the lower resolvent powers at the start together with the return/terminal power
sums `transientReturnPower X k` and `transientTerminalPower X k`.  Both of those are already
defined for every `k`, and `transient_resolvent_at_other_split` is likewise general, so the
fourth-order identity is a direct continuation of the same induction.

This is the first of the two ingredients needed to discharge `K3Inputs.step`.
-/

open Finset

namespace SSP.K2Concrete

/-- The fourth-order state-return resolvent identity.  Continues
`transient_third_resolvent_renewal` by one power of the resolvent. -/
theorem transient_fourth_resolvent_renewal {s : ℕ} (X : TransientStart s) :
    transientTerminalProbability X *
        ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) X.i =
      (transientHoldingMean X + transientReturnPower X 1) *
          ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
            ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i +
        transientReturnPower X 2 *
          ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i +
        transientReturnPower X 3 *
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i +
        transientReturnPower X 4 + transientTerminalPower X 4 := by
  let N := (1 - X.Q)⁻¹
  let NB := (1 - transientDeletedQ X)⁻¹
  let one : Fin s → ℝ := fun _ => 1
  let zvec := N.mulVec one
  let yvec := N.mulVec zvec
  let wvec := N.mulVec yvec
  let z := zvec X.i
  let y := yvec X.i
  let w := wvec X.i
  let t := (N.mulVec wvec) X.i
  let zo : Fin (s - 1) → ℝ := fun k => zvec (otherStateIndex X.i k)
  let yo : Fin (s - 1) → ℝ := fun k => yvec (otherStateIndex X.i k)
  let wo : Fin (s - 1) → ℝ := fun k => wvec (otherStateIndex X.i k)
  -- first split: the one-vector
  have hzo : zo = NB.mulVec (fun _ => (1 : ℝ)) +
      fun k => transientReturnPotential X k * z := by
    funext k
    simpa [N, NB, one, zvec, z, zo] using
      transient_resolvent_at_other_split X (fun _ => (1 : ℝ)) k
  have hNBzo : NB.mulVec zo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        fun k => (NB.mulVec (transientReturnPotential X)) k * z := by
    rw [hzo, Matrix.mulVec_add]
    congr 1
    · rw [pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (transientReturnPotential X) z
  -- second split: the z-vector
  have hyo : yo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        (fun k => (NB.mulVec (transientReturnPotential X)) k * z) +
        fun k => transientReturnPotential X k * y := by
    funext k
    have hk := transient_resolvent_at_other_split X zvec k
    change yo k = (NB.mulVec zo) k + transientReturnPotential X k * y at hk
    rw [hNBzo] at hk
    exact hk
  have hNByo : NB.mulVec yo =
      (NB ^ 3).mulVec (fun _ => (1 : ℝ)) +
        (fun k => ((NB ^ 2).mulVec (transientReturnPotential X)) k * z) +
        fun k => (NB.mulVec (transientReturnPotential X)) k * y := by
    rw [hyo, Matrix.mulVec_add, Matrix.mulVec_add]
    congr 1
    · congr 1
      · simp only [pow_three, pow_two, Matrix.mulVec_mulVec]
      · rw [mulVec_mul_const, pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (transientReturnPotential X) y
  -- third split: the y-vector
  have hwo : wo =
      (NB ^ 3).mulVec (fun _ => (1 : ℝ)) +
        (fun k => ((NB ^ 2).mulVec (transientReturnPotential X)) k * z) +
        (fun k => (NB.mulVec (transientReturnPotential X)) k * y) +
        fun k => transientReturnPotential X k * w := by
    funext k
    have hk := transient_resolvent_at_other_split X yvec k
    change wo k = (NB.mulVec yo) k + transientReturnPotential X k * w at hk
    rw [hNByo] at hk
    exact hk
  have hNBwo : NB.mulVec wo =
      (NB ^ 4).mulVec (fun _ => (1 : ℝ)) +
        (fun k => ((NB ^ 3).mulVec (transientReturnPotential X)) k * z) +
        (fun k => ((NB ^ 2).mulVec (transientReturnPotential X)) k * y) +
        fun k => (NB.mulVec (transientReturnPotential X)) k * w := by
    rw [hwo, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add]
    congr 1
    · congr 1
      · congr 1
        · show NB.mulVec ((NB ^ 3).mulVec (fun _ => (1 : ℝ)))
            = (NB ^ 4).mulVec (fun _ => (1 : ℝ))
          rw [Matrix.mulVec_mulVec, ← pow_succ']
        · rw [mulVec_mul_const, Matrix.mulVec_mulVec, ← pow_succ']
      · rw [mulVec_mul_const, pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (transientReturnPotential X) w
  -- collapse the departure average of `NB · wo`
  have hkill :
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) * (NB.mulVec wo) j) =
        transientReturnPower X 4 + transientTerminalPower X 4 +
          transientReturnPower X 3 * z + transientReturnPower X 2 * y +
          transientReturnPower X 1 * w := by
    rw [hNBwo]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have htotal := transientReturnPower_add_terminalPower X 4
    have hfourth :
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            ((NB ^ 4).mulVec (fun _ => (1 : ℝ))) j =
          transientReturnPower X 4 + transientTerminalPower X 4 := by
      simpa [NB] using htotal.symm
    rw [hfourth]
    unfold transientReturnPower
    simp only [pow_one]
    have hpull : ∀ (M : Matrix (Fin (s-1)) (Fin (s-1)) ℝ) (c : ℝ),
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            ((M.mulVec (transientReturnPotential X)) j * c) =
          (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            (M.mulVec (transientReturnPotential X)) j) * c := by
      intro M c
      calc
        _ = ∑ j, (transientDepartureWeight X (otherStateIndex X.i j) *
            (M.mulVec (transientReturnPotential X)) j) * c := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [Finset.sum_mul]
    rw [hpull (NB ^ 3) z, hpull (NB ^ 2) y, hpull NB w]
  -- the start-state recursion
  have hs0 := transient_resolvent_at_start X wvec
  have ha0 := transient_departure_average_resolvent_other X wvec
  have hs : t = transientHoldingMean X * w +
      ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (N.mulVec wvec) (otherStateIndex X.i j) := by
    simpa [N, wvec, w, t] using hs0
  have ha :
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (N.mulVec wvec) (otherStateIndex X.i j)) =
        transientReturnPower X 4 + transientTerminalPower X 4 +
          transientReturnPower X 3 * z + transientReturnPower X 2 * y +
          transientReturnPower X 1 * w +
          transientReturnProbability X * t := by
    simpa [N, NB, wvec, z, y, w, t, wo, hkill] using ha0
  have hpqt := congrArg (fun r : ℝ => r * t)
    (transientReturnProbability_add_terminalProbability X)
  change transientTerminalProbability X * t =
    (transientHoldingMean X + transientReturnPower X 1) * w +
      transientReturnPower X 2 * y + transientReturnPower X 3 * z +
        transientReturnPower X 4 + transientTerminalPower X 4
  nlinarith [hpqt]

/-! ## Fourth moments of the conditioned excursion laws -/

/-- Nonnegativity of the fourth moment of an arbitrary subprobability initial law. -/
theorem transientInitialMoment4_nonneg {s : ℕ} (X : TransientInitial s) :
    0 ≤ transientInitialMoment4 s X := by
  unfold transientInitialMoment4
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (X.weight_nonneg i) (transientMoment4_nonneg (X.component i))

/-- The fourth moment of the return-conditioned excursion, in power-sum form. -/
theorem transientReturnConditionedInitial_moment4_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientInitialMoment4 (s - 1)
        (transientReturnConditionedInitial X hs hp) =
      24 * ((∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ 4).mulVec
          (transientReturnPotential X)) j) / transientReturnProbability X) := by
  have h := congrArg (fun z : ℝ => 24 * z)
    (transientReturnConditionedInitial_resolvent_pow X hs hp 4)
  simpa [transientInitialMoment4, transientMoment4, TransientInitial.component,
    show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_zero, one_mul,
    ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- The fourth moment of the terminal-conditioned excursion, in power-sum form. -/
theorem transientTerminalConditionedInitial_moment4_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) :
    transientInitialMoment4 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)) =
      24 * ((∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ 4).mulVec
          (transientAbsorptionPotential X)) j) / transientTerminalProbability X) := by
  have h := congrArg (fun z : ℝ => 24 * z)
    (transientTerminalConditionedInitial_resolvent_pow X hs
      (transientTerminalProbability_pos X) 4)
  simpa [transientInitialMoment4, transientMoment4, TransientInitial.component,
    show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_zero, one_mul,
    ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

/-! ## The fourth-moment renewal identity

The `k = 3` development states its renewal moments in the `geomM` form of
`SSPLean.K3S4Renewal`: with `r = p/q` the ratio of return to terminal probability and
`kernelM*` the moments of one holding time followed by an excursion, the parent moments are
`geomM1 .. geomM4`.  This agrees with the `renewalM*` form used for `k = 2` (same quantity,
different parametrisation), so only the fourth-order identity is new. -/

open SSP.K3S4Renewal in
/-- The fourth raw moment in `geomM4` form, from the four resolvent power recursions. -/
theorem geomM4_from_power_recursions
    (x p q R1 A1 R2 A2 R3 A3 R4 A4 z y w t : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p + q = 1) (hz : q * z = x + R1 + A1)
    (hy : q * y = (x + R1) * z + R2 + A2)
    (hw : q * w = (x + R1) * y + R2 * z + R3 + A3)
    (ht : q * t = (x + R1) * w + R2 * y + R3 * z + R4 + A4) :
    24 * t = geomM4 (p / q)
      (kernelM1 x (R1 / p)) (kernelM2 x (R1 / p) (2 * (R2 / p)))
      (kernelM3 x (R1 / p) (2 * (R2 / p)) (6 * (R3 / p)))
      (kernelM4 x (R1 / p) (2 * (R2 / p)) (6 * (R3 / p)) (24 * (R4 / p)))
      (kernelM1 x (A1 / q)) (kernelM2 x (A1 / q) (2 * (A2 / q)))
      (kernelM3 x (A1 / q) (2 * (A2 / q)) (6 * (A3 / q)))
      (kernelM4 x (A1 / q) (2 * (A2 / q)) (6 * (A3 / q)) (24 * (A4 / q))) := by
  have zEq : z = (x + R1 + A1) / q := (eq_div_iff hq).2 (by linarith)
  have yEq : y = ((x + R1) * z + R2 + A2) / q := (eq_div_iff hq).2 (by linarith)
  have wEq : w = ((x + R1) * y + R2 * z + R3 + A3) / q := (eq_div_iff hq).2 (by linarith)
  have tEq : t = ((x + R1) * w + R2 * y + R3 * z + R4 + A4) / q :=
    (eq_div_iff hq).2 (by linarith)
  have peq : p = 1 - q := by linarith
  have honeq : (1 : ℝ) - q ≠ 0 := by rw [← peq]; exact hp
  rw [peq, tEq, wEq, yEq, zEq]
  unfold geomM4 geomM3 geomM2 geomM1 kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [honeq, hq]
  ring

open SSP.K3S4Renewal in
/-- The concrete fourth raw moment has the exact `geomM4` renewal form, when return is
possible.  Companion to `transientMoment1/2/3_renewal_of_return_pos` for `k = 2`. -/
theorem transientMoment4_renewal_of_return_pos {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientMoment4 s X =
      geomM4 (transientReturnProbability X / transientTerminalProbability X)
        (kernelM1 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientReturnConditionedInitial X hs hp)))
        (kernelM2 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientReturnConditionedInitial X hs hp))
          (transientInitialMoment2 (s-1) (transientReturnConditionedInitial X hs hp)))
        (kernelM3 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientReturnConditionedInitial X hs hp))
          (transientInitialMoment2 (s-1) (transientReturnConditionedInitial X hs hp))
          (transientInitialMoment3 (s-1) (transientReturnConditionedInitial X hs hp)))
        (kernelM4 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientReturnConditionedInitial X hs hp))
          (transientInitialMoment2 (s-1) (transientReturnConditionedInitial X hs hp))
          (transientInitialMoment3 (s-1) (transientReturnConditionedInitial X hs hp))
          (transientInitialMoment4 (s-1) (transientReturnConditionedInitial X hs hp)))
        (kernelM1 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X))))
        (kernelM2 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X)))
          (transientInitialMoment2 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X))))
        (kernelM3 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X)))
          (transientInitialMoment2 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X)))
          (transientInitialMoment3 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X))))
        (kernelM4 (transientHoldingMean X)
          (transientInitialMoment1 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X)))
          (transientInitialMoment2 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X)))
          (transientInitialMoment3 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X)))
          (transientInitialMoment4 (s-1) (transientTerminalConditionedInitial X hs
            (transientTerminalProbability_pos X)))) := by
  rw [transientReturnConditionedInitial_moment1_eq,
    transientTerminalConditionedInitial_moment1_eq,
    transientReturnConditionedInitial_moment2_eq,
    transientTerminalConditionedInitial_moment2_eq,
    transientReturnConditionedInitial_moment3_eq,
    transientTerminalConditionedInitial_moment3_eq,
    transientReturnConditionedInitial_moment4_eq X hs hp,
    transientTerminalConditionedInitial_moment4_eq X hs]
  have hpne := hp.ne'
  have hqne := (transientTerminalProbability_pos X).ne'
  have hmain := geomM4_from_power_recursions
    (transientHoldingMean X) (transientReturnProbability X)
    (transientTerminalProbability X)
    (transientReturnPower X 1) (transientTerminalPower X 1)
    (transientReturnPower X 2) (transientTerminalPower X 2)
    (transientReturnPower X 3) (transientTerminalPower X 3)
    (transientReturnPower X 4) (transientTerminalPower X 4)
    (((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
      ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
      ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) X.i)
    hpne hqne (transientReturnProbability_add_terminalProbability X)
    (transient_first_resolvent_renewal X) (transient_second_resolvent_renewal X)
    (transient_third_resolvent_renewal X) (transient_fourth_resolvent_renewal X)
  simpa [transientMoment4, transientReturnPower, transientTerminalPower, pow_one]
    using hmain

open SSP.K3S4Renewal in
/-- When return is impossible the fourth moment is that of a single holding time followed by
the terminal excursion: `kernelM4` at the terminal law.  Companion to
`transient_renewal_moments_of_return_zero`. -/
theorem transientMoment4_of_return_zero {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp0 : transientReturnProbability X = 0) :
    transientMoment4 s X =
      kernelM4 (transientHoldingMean X)
        (transientInitialMoment1 (s-1) (transientTerminalConditionedInitial X hs
          (transientTerminalProbability_pos X)))
        (transientInitialMoment2 (s-1) (transientTerminalConditionedInitial X hs
          (transientTerminalProbability_pos X)))
        (transientInitialMoment3 (s-1) (transientTerminalConditionedInitial X hs
          (transientTerminalProbability_pos X)))
        (transientInitialMoment4 (s-1) (transientTerminalConditionedInitial X hs
          (transientTerminalProbability_pos X))) := by
  have hq1 : transientTerminalProbability X = 1 := by
    linarith [transientReturnProbability_add_terminalProbability X]
  have hR1 := transientReturnPower_eq_zero_of_returnProbability_eq_zero X hp0 1
  have hR2 := transientReturnPower_eq_zero_of_returnProbability_eq_zero X hp0 2
  have hR3 := transientReturnPower_eq_zero_of_returnProbability_eq_zero X hp0 3
  have hR4 := transientReturnPower_eq_zero_of_returnProbability_eq_zero X hp0 4
  have hrec1 := transient_first_resolvent_renewal X
  have hrec2 := transient_second_resolvent_renewal X
  have hrec3 := transient_third_resolvent_renewal X
  have hrec4 := transient_fourth_resolvent_renewal X
  simp only [hq1, one_mul, hR1, hR2, hR3, hR4, add_zero, zero_mul] at hrec1 hrec2 hrec3 hrec4
  unfold transientTerminalPower at hrec1 hrec2 hrec3 hrec4
  simp only [pow_one] at hrec1 hrec2 hrec3 hrec4
  rw [transientTerminalConditionedInitial_moment1_eq,
    transientTerminalConditionedInitial_moment2_eq,
    transientTerminalConditionedInitial_moment3_eq,
    transientTerminalConditionedInitial_moment4_eq X hs]
  unfold transientMoment4 kernelM4
  rw [hq1]
  norm_num at hrec1 hrec2 hrec3 hrec4 ⊢
  rw [hrec4, hrec3, hrec2, hrec1]
  ring

end SSP.K2Concrete
