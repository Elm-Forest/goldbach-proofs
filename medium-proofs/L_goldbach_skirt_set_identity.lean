import Mathlib

/- A geometry reduction for the still-open medium-modulus Goldbach skirt:
   when the thin arc set lies in the mid-arc set, the inner removal
   is redundant, and the remaining region is a single set difference.
   This proves only the set geometry, not the signed analytic bound. -/

namespace GoldbachMediumSkirt

open MeasureTheory

theorem set_diff_diff_eq_diff_union
    (wide mid low narrow : Set ℝ) (h : narrow ⊆ mid) :
    ((wide \ mid) \ (low \ narrow)) = (wide \ (mid ∪ low)) := by
  ext t
  simp only [Set.mem_sdiff, Set.mem_union]
  constructor
  · rintro ⟨⟨hw, hnotmid⟩, hnotlow_narrow⟩
    refine ⟨hw, ?_⟩
    intro hh
    rcases hh with hm | hl
    · exact hnotmid hm
    · exact hnotlow_narrow ⟨hl, fun hn => hnotmid (h hn)⟩
  · rintro ⟨hw, hnotunion⟩
    refine ⟨⟨hw, ?_⟩, ?_⟩
    · intro hm
      exact hnotunion (Or.inl hm)
    · intro hl
      exact hnotunion (Or.inr hl.1)

theorem indicator_integral_eq
    (wide mid low narrow : Set ℝ) (h : narrow ⊆ mid)
    (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, ((wide \ mid) \ (low \ narrow)).indicator f t)
      =
    (∫ t in (0 : ℝ)..1, (wide \ (mid ∪ low)).indicator f t) := by
  rw [set_diff_diff_eq_diff_union wide mid low narrow h]


/-- Pointwise residual-energy inequality for the Goldbach prime-square
    integrand relative to a rational-arc model. -/
theorem square_difference_bound (s m : ℂ) :
    ‖s ^ 2 - m ^ 2‖ ≤ ‖s - m‖ ^ 2 + 2 * ‖s - m‖ * ‖m‖ := by
  have h : s ^ 2 - m ^ 2 = (s - m) ^ 2 + (2 : ℂ) * (s - m) * m := by ring
  rw [h]
  calc
    _ ≤ ‖(s - m) ^ 2‖ + ‖(2 : ℂ) * (s - m) * m‖ := norm_add_le _ _
    _ = _ := by
      have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      simp only [norm_pow, norm_mul, htwo]

end GoldbachMediumSkirt
