import Mathlib

/-! If a real measurement is within half a unit of an integer, with
strict distance on one side, the integer is uniquely determined. -/

theorem PEqualNP.Outside.L_goldbach_beaumont_perturbed_clock_gap :
    ∀ (n : ℕ) (s : ℤ) (x : ℝ),
      |x-(s:ℝ)| < 1/2 → |x-(n:ℝ)| ≤ 1/2 → s=(n:ℤ) := by
  intro n s x hs hn
  have hs' := abs_lt.mp hs
  have hn' := abs_le.mp hn
  have hlow : (-1 : ℝ) < (((s - (n : ℤ)) : ℤ) : ℝ) := by
    push_cast
    linarith
  have hhigh : (((s - (n : ℤ)) : ℤ) : ℝ) < 1 := by
    push_cast
    linarith
  have hlo : (-1 : ℤ) < s - (n : ℤ) := by
    exact_mod_cast hlow
  have hhi : s - (n : ℤ) < 1 := by
    exact_mod_cast hhigh
  omega
