import Mathlib

/-! An integer multiple of n lying in a narrow window around an
interior point of (0, 2n) must be n. -/

theorem PEqualNP.Outside.L_goldbach_beaumont_near_hit_window :
    ∀ (n p q r : ℕ) (k : ℤ), 0 < n → 2*r < n → r < p+q →
      p+q+r < 2*n →
      |(p:ℤ)+(q:ℤ)-k*(n:ℤ)| ≤ (r:ℤ) →
      |(p:ℤ)+(q:ℤ)-(n:ℤ)| ≤ (r:ℤ) := by
  intro n p q r k hn _ hrp htop hk
  have hrpZ : (r : ℤ) < (p : ℤ) + (q : ℤ) := by exact_mod_cast hrp
  have htopZ : (p : ℤ) + (q : ℤ) + (r : ℤ) < 2*(n : ℤ) := by exact_mod_cast htop
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hAbs := abs_le.mp hk
  have hklo : 1 ≤ k := by
    by_contra h
    have hkle : k ≤ 0 := by omega
    have hprod : k * (n : ℤ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hkle (le_of_lt hnZ)
    omega
  have hkhi : k ≤ 1 := by
    by_contra h
    have hkge : 2 ≤ k := by omega
    have hprod : 2 * (n : ℤ) ≤ k * (n : ℤ) :=
      mul_le_mul_of_nonneg_right hkge (le_of_lt hnZ)
    omega
  have heq : k = 1 := by omega
  simpa [heq] using hk
