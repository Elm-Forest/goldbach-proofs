import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_antispike_optimal_weight :
    ∀ (s : Finset ℕ) (c : ℕ → ℝ) (B : ℝ), 0 ≤ B →
      (∃ w : ℕ → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i ∈ s, (w i)^2) ≤ B^2 ∧
        (∑ i ∈ s, w i*c i) = -(B*Real.sqrt (∑ i ∈ s, (max 0 (-c i))^2))) ∧
      (∀ v : ℕ → ℝ, (∀ i, 0 ≤ v i) → (∑ i ∈ s, (v i)^2) ≤ B^2 →
        -(B*Real.sqrt (∑ i ∈ s, (max 0 (-c i))^2)) ≤ ∑ i ∈ s, v i*c i) := by
  intro s c B hB
  let d : ℕ → ℝ := fun i => max 0 (-c i)
  let P : ℝ := ∑ i ∈ s, (d i)^2
  let R : ℝ := Real.sqrt P
  have hd (i : ℕ) : 0 ≤ d i := le_max_left _ _
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = P := Real.sq_sqrt hP
  have hdc (i : ℕ) : d i*c i = -(d i)^2 := by
    dsimp [d]
    by_cases h : 0 ≤ -c i
    · rw [max_eq_right h]
      ring
    · rw [max_eq_left (le_of_lt (lt_of_not_ge h))]
      ring
  change (∃ w : ℕ → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i ∈ s, (w i)^2) ≤ B^2 ∧
      (∑ i ∈ s, w i*c i) = -(B*R)) ∧
      (∀ v : ℕ → ℝ, (∀ i, 0 ≤ v i) → (∑ i ∈ s, (v i)^2) ≤ B^2 →
        -(B*R) ≤ ∑ i ∈ s, v i*c i)
  constructor
  · by_cases hzero : R = 0
    · refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩
      · simpa using sq_nonneg B
      · simp [hzero]
    · have hpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
      let a : ℝ := B/R
      have ha : 0 ≤ a := div_nonneg hB hR
      have haR : a*R = B := by
        dsimp [a]
        field_simp
      refine ⟨fun i => a*d i, fun i => mul_nonneg ha (hd i), ?_, ?_⟩
      · calc
          (∑ i ∈ s, (a*d i)^2) = a^2*P := by
            simp only [mul_pow, Finset.mul_sum, P]
          _ = (a*R)^2 := by rw [← hR2, mul_pow]
          _ = B^2 := by rw [haR]
          _ ≤ B^2 := le_rfl
      · calc
          (∑ i ∈ s, (a*d i)*c i) = a * (∑ i ∈ s, d i*c i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = -(a*P) := by
            simp only [hdc, Finset.sum_neg_distrib, P, mul_neg]
          _ = -(B*R) := by
            rw [← hR2, ← haR]
            ring
  · intro v hv hbudget
    let T : ℝ := ∑ i ∈ s, v i*d i
    have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hd i))
    have hCS : T^2 ≤ (∑ i ∈ s, (v i)^2)*P :=
      Finset.sum_mul_sq_le_sq_mul_sq s v d
    have hbound : T^2 ≤ (B*R)^2 := by
      calc
        _ ≤ (∑ i ∈ s, (v i)^2)*P := hCS
        _ ≤ B^2*P := mul_le_mul_of_nonneg_right hbudget hP
        _ = (B*R)^2 := by rw [← hR2, mul_pow]
    have hTle : T ≤ B*R := by
      nlinarith [mul_nonneg hB hR]
    have hcomp : -T ≤ ∑ i ∈ s, v i*c i := by
      dsimp [T]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have h : -d i ≤ c i := by
        have hh : -c i ≤ d i := le_max_right _ _
        linarith
      calc
        -(v i*d i) = v i*(-d i) := by ring
        _ ≤ v i*c i := mul_le_mul_of_nonneg_left h (hv i)
    linarith
