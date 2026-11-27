import Conjectures.Goldbach.ShortProgressionsMeanTheta
import Conjectures.Goldbach.LowSkirtFromShortProgressions

/- Registered theorem #3789, now merged and accepted on upstream main, proves the
strong short-AP paper estimate. Check its definitional connection to the previously
conditional LowSkirtFromShortProgressions reduction. This auxiliary is not the
official WideRemainderInnerFloor theorem. -/

namespace InnerFloorResearch

theorem paperInput : GBSkirtVariance.PaperInput := by
  exact Conjectures.Goldbach.ShortProgressionsMeanTheta

theorem shortVariance : GBSkirtVariance.ShortVariance :=
  GBSkirtVariance.variance_of_full_average
    (GBSkirtVariance.full_average_of_dyadic
      (GBSkirtVariance.integer_of_paper paperInput))

theorem lowSkirtUnconditional :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(ε*(n:ℝ)) ≤ (GoldbachLowSkirt7.lowIntegral n).re :=
  GBSkirtVariance.low_skirt_of_paper paperInput

end InnerFloorResearch
