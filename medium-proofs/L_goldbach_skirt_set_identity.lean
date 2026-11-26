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
  constructor
  · intro ht
    obtain ⟨⟨hw, hnotmid⟩, hnotlow_narrow⟩ := Set.mem_diff.mp ht
    have hnotlow : t ∉ low := by
      intro hlow
      apply hnotlow_narrow
      exact Set.mem_diff.mpr ⟨hlow, fun hn => hnotmid (h hn)⟩
    exact Set.mem_diff.mpr ⟨hw, fun hh => hh.elim hnotmid hnotlow⟩
  · intro ht
    obtain ⟨hw, hnotunion⟩ := Set.mem_diff.mp ht
    have hnotmid : t ∉ mid := fun hm => hnotunion (Or.inl hm)
    have hnotlow : t ∉ low := fun hl => hnotunion (Or.inr hl)
    exact Set.mem_diff.mpr
      ⟨Set.mem_diff.mpr ⟨hw, hnotmid⟩,
       fun hh => hnotlow (Set.mem_diff.mp hh).1⟩

theorem indicator_integral_eq
    (wide mid low narrow : Set ℝ) (h : narrow ⊆ mid)
    (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, ((wide \ mid) \ (low \ narrow)).indicator f t)
      =
    (∫ t in (0 : ℝ)..1, (wide \ (mid ∪ low)).indicator f t) := by
  rw [set_diff_diff_eq_diff_union wide mid low narrow h]

end GoldbachMediumSkirt
