import SSPLean.K3CyclicComplexMiddlePairing

/-! # Exponential representation of the complex-middle derivative sequence -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

lemma cosineSign_add_two (n : ℕ) :
    cosineSign (n + 2) = -cosineSign n := by
  have hmod : n % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 4 <;>
    simp [cosineSign, Nat.add_mod, h]

lemma sineSign_add_two (n : ℕ) :
    sineSign (n + 2) = -sineSign n := by
  have hmod : n % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 4 <;>
    simp [sineSign, Nat.add_mod, h]

noncomputable def cosineTerm (z : ℝ) (n : ℕ) : ℝ :=
  (cosineSign n : ℝ) * z ^ (n / 2)

noncomputable def sineTerm (z : ℝ) (n : ℕ) : ℝ :=
  (sineSign n : ℝ) * z ^ ((n - 1) / 2)

lemma cosineTerm_add_two (z : ℝ) (n : ℕ) :
    cosineTerm z (n + 2) = -z * cosineTerm z n := by
  unfold cosineTerm
  rw [cosineSign_add_two]
  norm_num
  rw [pow_succ]
  ring

lemma sineTerm_add_two (z : ℝ) (n : ℕ) :
    sineTerm z (n + 2) = -z * sineTerm z n := by
  rcases n with _ | n
  · norm_num [sineTerm, sineSign]
  · unfold sineTerm
    rw [sineSign_add_two]
    norm_num
    rw [pow_succ]
    ring

noncomputable def oscillationReal (A B z : ℝ) (n : ℕ) : ℝ :=
  -A * cosineTerm z n + B * sineTerm z n

lemma oscillationReal_add_two (A B z : ℝ) (n : ℕ) :
    oscillationReal A B z (n + 2) =
      -z * oscillationReal A B z n := by
  rw [oscillationReal, oscillationReal, cosineTerm_add_two,
    sineTerm_add_two]
  ring

noncomputable def middleFrequency (omega : ℝ) : ℂ :=
  Complex.I * (omega : ℂ)

noncomputable def middleAmplitude (A B omega : ℝ) : ℂ :=
  ((-A : ℝ) : ℂ) / 2 - Complex.I * ((B / omega : ℝ) : ℂ) / 2

noncomputable def complexOscillation
    (A B omega : ℝ) (n : ℕ) : ℂ :=
  middleAmplitude A B omega * middleFrequency omega ^ n +
    (starRingEnd ℂ) (middleAmplitude A B omega) *
      (-middleFrequency omega) ^ n

lemma middleFrequency_sq (omega : ℝ) :
    middleFrequency omega ^ 2 = -((omega ^ 2 : ℝ) : ℂ) := by
  unfold middleFrequency
  rw [mul_pow, Complex.I_sq]
  push_cast
  ring

lemma complexOscillation_add_two (A B omega : ℝ) (n : ℕ) :
    complexOscillation A B omega (n + 2) =
      -((omega ^ 2 : ℝ) : ℂ) * complexOscillation A B omega n := by
  unfold complexOscillation
  rw [show n + 2 = n + 2 by rfl, pow_add, pow_add,
    middleFrequency_sq]
  rw [show (-middleFrequency omega) ^ 2 =
      -((omega ^ 2 : ℝ) : ℂ) by
    rw [Even.neg_pow (by norm_num : Even 2), middleFrequency_sq]]
  ring

lemma complexOscillation_zero (A B omega : ℝ) :
    complexOscillation A B omega 0 = ((-A : ℝ) : ℂ) := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 :=
    map_ofNat (starRingEnd ℂ) 2
  simp only [complexOscillation, pow_zero, mul_one, middleAmplitude, map_div₀,
    map_sub, Complex.conj_ofReal, map_mul, map_neg, Complex.conj_I, Complex.ofReal_neg]
  rw [htwo]
  ring

lemma complexOscillation_one
    (A B omega : ℝ) (homega : omega ≠ 0) :
    complexOscillation A B omega 1 = (B : ℂ) := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 :=
    map_ofNat (starRingEnd ℂ) 2
  simp only [complexOscillation, pow_one, middleAmplitude, middleFrequency, map_div₀,
    map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.ofReal_div]
  rw [htwo]
  field_simp [homega]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem complexOscillation_eq_real
    (A B omega : ℝ) (homega : omega ≠ 0) (n : ℕ) :
    complexOscillation A B omega n =
      (oscillationReal A B (omega ^ 2) n : ℂ) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [complexOscillation_zero]
      norm_num [oscillationReal, cosineTerm, sineTerm, cosineSign, sineSign]
  | one =>
      rw [complexOscillation_one A B omega homega]
      norm_num [oscillationReal, cosineTerm, sineTerm, cosineSign, sineSign]
  | more n ih0 ih1 =>
      rw [complexOscillation_add_two, oscillationReal_add_two, ih0]
      push_cast
      ring

theorem scalarDerivative_complex_representation
    (rhoValue etaValue omega : ℝ)
    (homega : omega ≠ 0)
    (hz : scalarZ rhoValue = omega ^ 2) (n : ℕ) :
    (scalarDerivative rhoValue etaValue n : ℂ) =
      (scalarA rhoValue etaValue : ℂ) +
        complexOscillation (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) omega n := by
  rw [complexOscillation_eq_real _ _ _ homega]
  unfold scalarDerivative oscillationReal cosineTerm sineTerm
  rw [← hz]
  push_cast
  ring

end SSP.K3CyclicComplex.MiddleCoeff
