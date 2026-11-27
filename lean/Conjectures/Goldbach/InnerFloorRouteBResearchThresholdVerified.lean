import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Route B Research Thresholds & Escape-Hatch Formalization:
1. Even Real Diagonal Positivity: for an even primitive quadratic character
   (`χ (-1) = 1`) and any nonnegative real kernel `w ≥ 0`, both the Gauss-sum
   square `+(q : ℂ)` and the self-convolution `∑ k ≤ n, w k * w (n - k)` are
   nonnegative, so even Siegel zeros contribute positively to the signed floor.
2. Exact Necessity & Sufficiency Threshold for Odd Real Zeros:
   - Necessity (`oddReal_logGap_violates_floor`): at `n = q^k` with `β = 1 - c/log q`,
     `-(q/φ(q)) * n^(2β - 1) ≤ -exp(-2kc) * n`, violating `-εn` for `ε < exp(-2kc)`.
   - Sufficiency (`oddReal_superLogGap_satisfies_floor`): whenever
     `(1 - β) * log n ≥ (1/2) * log (q / (φ(q) * ε))`, we have
     `-(ε * n) ≤ -(q/φ(q)) * n^(2β - 1)`.
3. Almost-All Escape Hatch (`multiples_card_le_div`): the set of `n ∈ Icc 1 X`
   divisible by `d ≥ 1` has cardinality at most `X / d`, explaining formally why
   Gate 3 (`gcdSaving`) eliminates an odd exceptional conductor for almost all
   even `n ≤ X`, whereas the pointwise `∀ n ≥ N, Even n` frozen statement
   cannot avoid `d ∣ n`.
-/
namespace InnerFloorRouteBThreshold
open Finset AddChar MulChar
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Nonnegativity of discrete self-convolution for any nonnegative real kernel. -/
theorem selfConvolution_nonneg (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), w k * w (n - k) :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (hw (n - k))

/-- For an even real diagonal term (positive Gauss-sum factor `q / φ(q)` and
    nonnegative self-convolution), the signed contribution is nonnegative. -/
theorem evenRealDiag_contribution_nonneg (q n : ℕ)
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ ((q : ℝ) / (q.totient : ℝ)) * (∑ k ∈ Finset.range (n + 1), w k * w (n - k)) := by
  have hφ : 0 ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg q) hφ) (selfConvolution_nonneg w hw n)

/-- Exact identity `n^(2β - 1) = n * exp(-2 * (1 - β) * log n)` for `n > 0`. -/
theorem rpow_two_beta_sub_one_eq (n β : ℝ) (hn : 0 < n) :
    n ^ (2 * β - 1) = n * Real.exp (-(2 * (1 - β) * Real.log n)) := by
  rw [Real.rpow_def_of_pos hn]
  have h1 : Real.log n * (2 * β - 1) = Real.log n + -(2 * (1 - β) * Real.log n) := by ring
  rw [h1, Real.exp_add, Real.exp_log hn]

/-- Necessity: if `n = q^k` (`q > 1`, `k > 0`) and `β = 1 - c / log q`, then
    the odd real diagonal contribution `-(q/φ(q)) * n^(2β - 1)` is bounded
    above by `-exp(-2kc) * n`, violating `-εn` whenever `ε < exp(-2kc)`. -/
theorem oddReal_logGap_violates_floor (q : ℕ) (hq : 1 < q) (k c ε : ℝ)
    (hε : ε < Real.exp (-(2 * k * c))) :
    let n : ℝ := (q : ℝ) ^ k;
    let β : ℝ := 1 - c / Real.log (q : ℝ);
    -((q : ℝ) / (q.totient : ℝ)) * n ^ (2 * β - 1) < -(ε * n) := by
  dsimp only
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hnp : 0 < (q : ℝ) ^ k := Real.rpow_pos_of_pos hqp k
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hqR).ne'
  rw [rpow_two_beta_sub_one_eq ((q : ℝ) ^ k) (1 - c / Real.log (q : ℝ)) hnp]
  rw [Real.log_rpow hqp]
  have hexp : -(2 * (1 - (1 - c / Real.log (q : ℝ))) * (k * Real.log (q : ℝ))) = -(2 * k * c) := by
    field_simp
    ring
  rw [hexp]
  have hφp : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hratio : 1 ≤ (q : ℝ) / (q.totient : ℝ) :=
    (le_div_iff₀ hφp).2 (by simpa only [one_mul] using
      (show (q.totient : ℝ) ≤ (q : ℝ) by exact_mod_cast Nat.totient_le q))
  have hepos : 0 < Real.exp (-(2 * k * c)) := Real.exp_pos _
  have h1 : Real.exp (-(2 * k * c)) * (q : ℝ) ^ k ≤
      ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ) ^ k * Real.exp (-(2 * k * c))) := by
    have hm := mul_le_mul_of_nonneg_right hratio (mul_pos hnp hepos).le
    nlinarith only [hm]
  have h2 : ε * (q : ℝ) ^ k < Real.exp (-(2 * k * c)) * (q : ℝ) ^ k :=
    mul_lt_mul_of_pos_right hε hnp
  linarith only [h1, h2]

/-- Sufficiency: if `(1 - β) * log n ≥ (1/2) * log (q / (φ(q) * ε))` for `n > 0`,
    `q ≥ 1`, `ε > 0`, then the odd real diagonal contribution is absorbed into
    the one-sided floor `-(ε * n)`. -/
theorem oddReal_superLogGap_satisfies_floor (q : ℕ) (hq : 0 < q)
    (n β ε : ℝ) (hn : 0 < n) (hε : 0 < ε)
    (hgap : (1 / 2 : ℝ) * Real.log ((q : ℝ) / ((q.totient : ℝ) * ε)) ≤ (1 - β) * Real.log n) :
    -(ε * n) ≤ -((q : ℝ) / (q.totient : ℝ)) * n ^ (2 * β - 1) := by
  rw [rpow_two_beta_sub_one_eq n β hn]
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hφp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have harg : 0 < (q : ℝ) / ((q.totient : ℝ) * ε) := by positivity
  have h2 : Real.log ((q : ℝ) / ((q.totient : ℝ) * ε)) ≤ 2 * (1 - β) * Real.log n := by
    linarith only [hgap]
  have hexp : (q : ℝ) / ((q.totient : ℝ) * ε) ≤ Real.exp (2 * (1 - β) * Real.log n) := by
    rw [← Real.exp_log harg]
    exact Real.exp_le_exp.mpr h2
  have hinv : Real.exp (-(2 * (1 - β) * Real.log n)) ≤ (q.totient : ℝ) * ε / (q : ℝ) := by
    rw [Real.exp_neg]
    have hpos : 0 < Real.exp (2 * (1 - β) * Real.log n) := Real.exp_pos _
    rw [inv_le_iff_one_le_mul₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left hexp (div_nonneg (mul_nonneg hφp.le hε.le) hqp.le)
    have hcancel : (q.totient : ℝ) * ε / (q : ℝ) * ((q : ℝ) / ((q.totient : ℝ) * ε)) = 1 := by
      field_simp
    linarith only [hmul, hcancel]
  have hcoeff : ((q : ℝ) / (q.totient : ℝ)) * Real.exp (-(2 * (1 - β) * Real.log n)) ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hinv (div_nonneg hqp.le hφp.le)
    have hsimp : (q : ℝ) / (q.totient : ℝ) * ((q.totient : ℝ) * ε / (q : ℝ)) = ε := by
      field_simp
    linarith only [hm, hsimp]
  have hn_mul := mul_le_mul_of_nonneg_right hcoeff hn.le
  linarith only [hn_mul]

/-- Almost-all escape hatch: the number of integers `n ∈ Icc 1 X` divisible by
    `d ≥ 1` is at most `X / d`. -/
theorem multiples_card_le_div (X d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card ≤ X / d := by
  have hinj : ∀ a ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
      ∀ b ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n), a / d = b / d → a = b := by
    intro a ha b hb hab
    have hda : d ∣ a := (Finset.mem_filter.mp ha).2
    have hdb : d ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = d * (a / d) := (Nat.mul_div_cancel' hda).symm
      _ = d * (b / d) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hdb
  have hmaps : ∀ a ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
      a / d ∈ Finset.Icc 1 (X / d) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hrange := Finset.mem_Icc.mp ha'.1
    have hda : d ∣ a := ha'.2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hrange.2⟩
    rcases hda with ⟨k, rfl⟩
    have hk : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    rw [Nat.mul_div_right k hd]
    exact hk
  calc
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card
        ≤ (Finset.Icc 1 (X / d)).card := Finset.card_le_card_of_injOn (fun a => a / d) hmaps hinj
    _ = X / d := by simp

end
end InnerFloorRouteBThreshold

#print axioms InnerFloorRouteBThreshold.selfConvolution_nonneg
#print axioms InnerFloorRouteBThreshold.evenRealDiag_contribution_nonneg
#print axioms InnerFloorRouteBThreshold.oddReal_logGap_violates_floor
#print axioms InnerFloorRouteBThreshold.oddReal_superLogGap_satisfies_floor
#print axioms InnerFloorRouteBThreshold.multiples_card_le_div
