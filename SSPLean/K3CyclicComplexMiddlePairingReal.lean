import SSPLean.K3CyclicComplexMiddleExactPairing

/-! # Real form of the exact complex-middle coefficient pairing -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

noncomputable def middleR (N : ℕ) (omega : ℝ) : ℂ :=
  geometricPairClosed N 1 (middleFrequency omega)

noncomputable def middleJ (N : ℕ) (omega : ℝ) : ℝ :=
  (middleR N omega).im / omega

lemma middleFrequency_conj (omega : ℝ) :
    (starRingEnd ℂ) (middleFrequency omega) = -middleFrequency omega := by
  simp [middleFrequency]

lemma middleR_conj (N : ℕ) (omega : ℝ) :
    geometricPairClosed N 1 (-middleFrequency omega) =
      (starRingEnd ℂ) (middleR N omega) := by
  have hone : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
  unfold middleR geometricPairClosed
  simp only [map_add, map_pow, map_mul, map_sub, map_div₀,
    Complex.conj_natCast, Complex.conj_ofNat, middleFrequency_conj]
  rw [hone]

@[simp] lemma middleAmplitude_re (A B omega : ℝ) :
    (middleAmplitude A B omega).re = -A / 2 := by
  simp [middleAmplitude]

@[simp] lemma middleAmplitude_im (A B omega : ℝ) :
    (middleAmplitude A B omega).im = -B / (2 * omega) := by
  simp [middleAmplitude]
  ring

lemma oscillatory_pair_conj
    (A B omega : ℝ) (N : ℕ) :
    (starRingEnd ℂ) (middleAmplitude A B omega) ^ 2 *
        (-2 * middleFrequency omega) ^ N =
      (starRingEnd ℂ)
        (middleAmplitude A B omega ^ 2 *
          (2 * middleFrequency omega) ^ N) := by
  rw [map_mul, map_pow, map_pow, map_mul, map_ofNat,
    middleFrequency_conj]
  ring

lemma cross_pair_conj
    (A B omega : ℝ) (N : ℕ) :
    2 * (A : ℂ) * (starRingEnd ℂ) (middleAmplitude A B omega) *
        geometricPairClosed N 1 (-middleFrequency omega) =
      (starRingEnd ℂ)
        (2 * (A : ℂ) * middleAmplitude A B omega * middleR N omega) := by
  rw [middleR_conj, map_mul, map_mul, map_mul, map_ofNat,
    Complex.conj_ofReal]

/-- Equation `middle-coefficient-pairing` in real form. -/
theorem scalarCurvatureCoefficient_pairing
    {rhoValue etaValue omega : ℝ} {N : ℕ}
    (hN : 3 ≤ N) (homega : omega ≠ 0)
    (hz : scalarZ rhoValue = omega ^ 2) :
    scalarCurvatureCoefficient rhoValue etaValue N =
      scalarA rhoValue etaValue ^ 2 * 2 ^ N +
      2 * (middleAmplitude (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) omega ^ 2 *
        (2 * middleFrequency omega) ^ N).re -
      2 * scalarA rhoValue etaValue ^ 2 * (middleR N omega).re +
      2 * scalarA rhoValue etaValue * scalarB rhoValue etaValue *
        middleJ N omega := by
  have hpair := scalarCurvatureCoefficient_complex_pairing
    (rhoValue := rhoValue) (etaValue := etaValue) (omega := omega)
    (N := N) hN homega hz
  have hre := congrArg Complex.re hpair
  rw [oscillatory_pair_conj, cross_pair_conj] at hre
  simp only [Complex.add_re, Complex.conj_re] at hre
  rw [Complex.ofReal_re] at hre
  have hfirst :
      ((scalarA rhoValue etaValue : ℂ) ^ 2 * (2 : ℂ) ^ N).re =
        scalarA rhoValue etaValue ^ 2 * 2 ^ N := by norm_cast
  rw [hfirst] at hre
  have hcross :
      2 * (2 * (scalarA rhoValue etaValue : ℂ) *
        middleAmplitude (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) omega * middleR N omega).re =
        -2 * scalarA rhoValue etaValue ^ 2 * (middleR N omega).re +
          2 * scalarA rhoValue etaValue * scalarB rhoValue etaValue *
            middleJ N omega := by
    have hcre :
        (2 * (scalarA rhoValue etaValue : ℂ) *
          middleAmplitude (scalarA rhoValue etaValue)
            (scalarB rhoValue etaValue) omega).re =
          -scalarA rhoValue etaValue ^ 2 := by
      simp [Complex.mul_re]
      ring
    have hcim :
        (2 * (scalarA rhoValue etaValue : ℂ) *
          middleAmplitude (scalarA rhoValue etaValue)
            (scalarB rhoValue etaValue) omega).im =
          -scalarA rhoValue etaValue * scalarB rhoValue etaValue / omega := by
      simp [Complex.mul_im]
      ring
    rw [Complex.mul_re, hcre, hcim]
    unfold middleJ
    field_simp [homega]
    ring
  rw [show geometricPairClosed N 1 (middleFrequency omega) =
    middleR N omega by rfl] at hre
  linarith [hre, hcross]

end SSP.K3CyclicComplex.MiddleCoeff
