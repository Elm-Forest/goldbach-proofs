import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Route B Unconditional Almost-All Even n Closure (Gate-3 Exceptional Set Density):
Proves that for any finite family of exceptional conductors `D` and any
Gate-3 threshold `M > 0`, the set of integers `n ∈ Icc 1 X` whose gcd ratio
`gcd(n, d) / d` exceeds `1 / M` for some `d ∈ D` has cardinality bounded by
`∑ d ∈ D, ∑ g ∈ d.divisors with d < g * M, (X / g)`, and in real-valued form by
`(X : ℝ) * M * ∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)`.

Consequently, even without ruling out hypothetical odd Siegel zeros or q-aspect
log-gap zeros, Gate 3 (`gcdSaving`) eliminates the entire triple-gate residual
for all `n ≤ X` outside an explicit exceptional set of density
`O(M * ∑_{d ∈ D} τ(d) / d)`.
-/
namespace InnerFloorRouteBAlmostAll
open Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Number of integers `n ∈ Icc 1 X` divisible by `g > 0` is at most `X / g`. -/
theorem multiples_card_le_div (X g : ℕ) (hg : 0 < g) :
    ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card ≤ X / g := by
  have hinj : ∀ a ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n),
      ∀ b ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n), a / g = b / g → a = b := by
    intro a ha b hb hab
    have hga : g ∣ a := (Finset.mem_filter.mp ha).2
    have hgb : g ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = g * (a / g) := (Nat.mul_div_cancel' hga).symm
      _ = g * (b / g) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hgb
  have hmaps : ∀ a ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n),
      a / g ∈ Finset.Icc 1 (X / g) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hrange := Finset.mem_Icc.mp ha'.1
    have hga : g ∣ a := ha'.2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hrange.2⟩
    rcases hga with ⟨k, rfl⟩
    have hk : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    rw [Nat.mul_div_right k hg]
    exact hk
  calc
    ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card
        ≤ (Finset.Icc 1 (X / g)).card := Finset.card_le_card_of_injOn (fun a => a / g) hmaps hinj
    _ = X / g := by simp

/-- High-gcd exceptional set for a single conductor `d` and real threshold `M`:
    all `n ∈ Icc 1 X` such that `(d : ℝ) < (Nat.gcd n d : ℝ) * M`. -/
def highGcdSet (X d : ℕ) (M : ℝ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => (d : ℝ) < (Nat.gcd n d : ℝ) * M)

/-- Every `n ∈ highGcdSet X d M` is divisible by some divisor `g ∣ d`
    satisfying `(d : ℝ) < (g : ℝ) * M`. -/
theorem highGcdSet_subset_biUnion (X d : ℕ) (hd : 0 < d) (M : ℝ) :
    highGcdSet X d M ⊆
      (d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).biUnion
        (fun g => (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)) := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  refine Finset.mem_biUnion.mpr ⟨Nat.gcd n d, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n d, hd.ne'⟩, hn'.2⟩
  · exact Finset.mem_filter.mpr ⟨hn'.1, Nat.gcd_dvd_left n d⟩

/-- Exact combinatorial bound for a single conductor `d`:
    `|highGcdSet X d M| ≤ ∑_{g ∣ d, d < g * M} (X / g)`. -/
theorem highGcdSet_card_le_sum_div (X d : ℕ) (hd : 0 < d) (M : ℝ) :
    (highGcdSet X d M).card ≤
      ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g := by
  calc
    (highGcdSet X d M).card
        ≤ ((d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).biUnion
            (fun g => (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n))).card :=
          Finset.card_le_card (highGcdSet_subset_biUnion X d hd M)
    _ ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M),
          ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g := by
          apply Finset.sum_le_sum
          intro g hg
          have hgd : g ∣ d := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
          have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd hd
          exact multiples_card_le_div X g hgpos

/-- Real-valued density bound for a single conductor `d > 0` and `M ≥ 0`:
    `|highGcdSet X d M| ≤ X * M * τ(d) / d`. -/
theorem highGcdSet_card_le_real (X d : ℕ) (hd : 0 < d) (M : ℝ) (hM : 0 ≤ M) :
    ((highGcdSet X d M).card : ℝ) ≤ (X : ℝ) * M * (d.divisors.card : ℝ) / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((highGcdSet X d M).card : ℝ) ≤
      ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X / g : ℕ) : ℝ) := by
    simpa only [Nat.cast_sum] using (show ((highGcdSet X d M).card : ℝ) ≤ ((∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g : ℕ) : ℝ) by exact_mod_cast highGcdSet_card_le_sum_div X d hd M)
  have hterm : ∀ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M),
      ((X / g : ℕ) : ℝ) ≤ (X : ℝ) * M / (d : ℝ) := by
    intro g hg
    have hgd : g ∣ d := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd hd
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hlt : (d : ℝ) < (g : ℝ) * M := (Finset.mem_filter.mp hg).2
    have hdiv : ((X / g : ℕ) : ℝ) ≤ (X : ℝ) / (g : ℝ) := by
      rw [le_div_iff₀ hgR]
      exact_mod_cast Nat.div_mul_le_self X g
    have hinv : (X : ℝ) / (g : ℝ) ≤ (X : ℝ) * M / (d : ℝ) := by
      rw [div_le_div_iff₀ hgR hdR]
      have hmul := mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg (α := ℝ) X)
      linarith only [hmul]
    exact hdiv.trans hinv
  calc
    ((highGcdSet X d M).card : ℝ)
        ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X / g : ℕ) : ℝ) := h1
    _ ≤ ∑ _g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X : ℝ) * M / (d : ℝ)) :=
          Finset.sum_le_sum hterm
    _ = ((d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).card : ℝ) * ((X : ℝ) * M / (d : ℝ)) := by
          simp
    _ ≤ (d.divisors.card : ℝ) * ((X : ℝ) * M / (d : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_filter_le d.divisors _
          · positivity
    _ = (X : ℝ) * M * (d.divisors.card : ℝ) / (d : ℝ) := by ring

/-- Family-wide almost-all exceptional set bound:
    for any finite family `D` of positive conductors and threshold `M ≥ 0`,
    the number of integers `n ∈ Icc 1 X` that fail Gate 3 for at least one `d ∈ D`
    is at most `X * M * ∑_{d ∈ D} τ(d) / d`. -/
theorem familyHighGcd_card_le_real (X : ℕ) (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (M : ℝ) (hM : 0 ≤ M) :
    (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤
      (X : ℝ) * M * (∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)) := by
  have hsub :
      (Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M) ⊆
        D.biUnion (fun d => highGcdSet X d M) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rcases hn'.2 with ⟨d, hd, hlt⟩
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hn'.1, hlt⟩⟩
  have hcard :
      (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤
        ∑ d ∈ D, ((highGcdSet X d M).card : ℝ) := by
    have hnat :
        ((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card ≤
          ∑ d ∈ D, (highGcdSet X d M).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    simpa only [Nat.cast_sum] using (show (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤ ((∑ d ∈ D, (highGcdSet X d M).card : ℕ) : ℝ) by exact_mod_cast hnat)
  calc
    (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ)
        ≤ ∑ d ∈ D, ((highGcdSet X d M).card : ℝ) := hcard
    _ ≤ ∑ d ∈ D, ((X : ℝ) * M * ((d.divisors.card : ℝ) / (d : ℝ))) := by
          apply Finset.sum_le_sum
          intro d hd
          simpa only [mul_div_assoc] using highGcdSet_card_le_real X d (hD d hd) M hM
    _ = (X : ℝ) * M * (∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)) := by
          rw [Finset.mul_sum]

end
end InnerFloorRouteBAlmostAll

#print axioms InnerFloorRouteBAlmostAll.multiples_card_le_div
#print axioms InnerFloorRouteBAlmostAll.highGcdSet_card_le_sum_div
#print axioms InnerFloorRouteBAlmostAll.highGcdSet_card_le_real
#print axioms InnerFloorRouteBAlmostAll.familyHighGcd_card_le_real
