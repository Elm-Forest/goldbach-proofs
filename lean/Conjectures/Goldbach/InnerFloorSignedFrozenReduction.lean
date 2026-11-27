import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor
import Conjectures.Goldbach.ReflectionCharacterContraction
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4
import Conjectures.Goldbach.LowSkirtFromShortProgressions
import PEqualNP.Outside.L_goldbach_frontier_medcore_bv_band

/-! Research-only conditional candidate; no external zero-free strip assumed proven.
Generated from individually reviewed research modules.
Retain source attribution in each original body. -/

/-! BEGIN InnerFloorArithmeticCore.lean; sha256 c0b88eb71935e24c8dccec78b5acf9336458b379349ed642e85f1a97f0870139 -/
section
/-!
Small independently replayable arithmetic interface extracted from
ShortProgressionsMeanTheta (XBribo, PR #3789,
a546c6629fae0223b56067d5e4ebc34043c4fbf1, Apache-2.0).
Names relocated to avoid duplicate OAI.Ostmann declarations when used
with DyadicCellShortPrimeFloor. Only elementary definitions and lemmas
are copied; none of the analytic black-box conclusions are assumed.
-/
open Finset Filter
open scoped Topology Classical
noncomputable section
namespace InnerFloorAP
def theta (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊).filter (fun k : ℕ => (k : ZMod q) = r),
    if k.Prime then Real.log (k : ℝ) else 0

theorem mem_window {y h : ℝ} (hy : 0 ≤ y) (hh : 0 ≤ h) (k : ℕ) :
    k ∈ Finset.Icc (⌊y⌋₊ + 1) ⌊y+h⌋₊ ↔ y < (k : ℝ) ∧ (k : ℝ) ≤ y+h := by
  rw [Finset.mem_Icc, Nat.add_one_le_iff, Nat.floor_lt hy, Nat.le_floor_iff (by linarith)]

def centeredPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (y h : ℝ) : ℂ :=
  (∑ k ∈ Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊,
    ((if k.Prime then Real.log (k : ℝ) else 0 : ℝ) : ℂ) * χ (k : ZMod q)) -
    (if χ = 1 then (h : ℂ) else 0)

theorem centeredPrimeSum_changeLevel {d q : ℕ} [NeZero q] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) {h y : ℝ} (hq : (q : ℝ) ≤ y) (hh : 0 ≤ h) :
    centeredPrimeSum (DirichletCharacter.changeLevel hd χ) y h = centeredPrimeSum χ y h := by
  classical
  have hone : DirichletCharacter.changeLevel hd χ = 1 ↔ χ = 1 := by
    rw [← map_one (DirichletCharacter.changeLevel (R := ℂ) hd)]
    exact (DirichletCharacter.changeLevel_injective hd).eq_iff
  unfold centeredPrimeSum
  simp only [hone]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpr : p.Prime
  · have hpy := ((mem_window ((Nat.cast_nonneg q).trans hq) hh p).1 hp).1
    have hqp : q < p := by exact_mod_cast (hq.trans_lt hpy)
    have hcop := hpr.coprime_iff_not_dvd.mpr
      (fun hdvd => (Nat.not_le_of_gt hqp) (Nat.le_of_dvd (NeZero.pos q) hdvd))
    have he := χ.changeLevel_eq_cast_of_dvd' hd (Nat.isCoprime_iff_coprime.mpr hcop)
    simpa only [Int.cast_natCast] using congrArg
      (fun z : ℂ => ((if p.Prime then Real.log (p : ℝ) else 0 : ℝ) : ℂ) * z) he
  · simp [hpr]


end InnerFloorAP

namespace InnerFloorLinearTotient
set_option maxHeartbeats 1000000 in


private def squareMass : ℝ := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
set_option maxHeartbeats 1000000 in

private theorem squareMass_nonneg : 0 ≤ squareMass := tsum_nonneg fun _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem sum_square_inv_le (s : Finset ℕ) :
    (∑ n ∈ s, ((n:ℝ)^2)⁻¹) ≤ squareMass :=
  (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2:ℕ))).sum_le_tsum s fun _ _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem one_le_squareMass : 1 ≤ squareMass := by
  simpa using sum_square_inv_le {(1:ℕ)}

set_option maxHeartbeats 1000000 in
/-- Uniform constant for the reciprocal-totient mean and conductor lifting. -/
def weightConstant : ℝ := Real.exp (2*squareMass) * squareMass
set_option maxHeartbeats 1000000 in

theorem weightConstant_nonneg : 0 ≤ weightConstant :=
  mul_nonneg (Real.exp_pos _).le squareMass_nonneg
set_option maxHeartbeats 1000000 in

private theorem prime_factor_bound {p : ℕ} (hp : 2 ≤ p) :
    (1-(p:ℝ)⁻¹)⁻¹ ≤ (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) := by
  let u := (p:ℝ)⁻¹
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u ≤ 1/2 := by
    change (p:ℝ)⁻¹ ≤ 1/2
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hp'
  have hden : 0 < 1-u := by linarith
  have hsq : u^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hu hu' 2
  have hnon := mul_nonneg (sq_nonneg u) (show 0 ≤ 1-2*u^2 by linarith)
  rw [← inv_pow]
  change (1-u)⁻¹ ≤ (1+u)*(1+2*u^2)
  rw [← one_div, div_le_iff₀ hden]
  nlinarith only [hnon]
set_option maxHeartbeats 1000000 in

private theorem squarefree_product_eq (q : ℕ) (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) = ∑ d ∈ q.divisors with Squarefree d, (d:ℝ)⁻¹ := by
  rw [Finset.prod_one_add, Nat.sum_divisors_filter_squarefree hq.ne', Nat.factors_eq]
  refine sum_congr rfl fun s _ => ?_
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
  rw [Finset.prod_eq_multiset_prod, show (fun i : ℕ => i) = id from rfl, Multiset.map_id]
set_option maxHeartbeats 1000000 in

private theorem ratio_le_divisors (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hEuler : (q.totient:ℝ) = (q:ℝ)*∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹) := by
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors q)
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) : 0 ≤ (1-(p:ℝ)⁻¹)⁻¹ := by
    have hp' : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply inv_nonneg.mpr
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by linarith)
  have hsq : (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) ≤ Real.exp (2*squareMass) := by
    apply (Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)).trans
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_square_inv_le _) (by norm_num)
  calc
    _ = ∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹)⁻¹ := by
      rw [hEuler, div_mul_eq_div_div, div_self hq'.ne', one_div, Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) :=
      prod_le_prod₀ hlocal fun p hp => prime_factor_bound (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) :=
      Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * Real.exp (2*squareMass) :=
      mul_le_mul_of_nonneg_left hsq (prod_nonneg fun _ _ => by positivity)
    _ ≤ _ := by
      rw [mul_comm, squarefree_product_eq q hq]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)) (Real.exp_pos _).le
set_option maxHeartbeats 1000000 in

private theorem harmonic_bound (Q : ℕ) :
    (∑ i ∈ Icc 1 Q, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log Q

set_option maxHeartbeats 1000000 in
/-- Pointwise `q/φ(q)` also costs at most one logarithm. -/
theorem ratio_totient_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ weightConstant * (1+Real.log q) := by
  have hsub : q.divisors ⊆ Icc 1 q := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q from hq))
  calc
    _ ≤ Real.exp (2*squareMass) * (1+Real.log q) :=
      (ratio_le_divisors q hq).trans (mul_le_mul_of_nonneg_left
        ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (harmonic_bound q))
        (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (Real.exp_pos _).le one_le_squareMass) (by positivity)
set_option maxHeartbeats 1000000 in

private theorem sum_antidiagonal_le_product (Q : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal, f ab.1*g ab.2) ≤
      (∑ a ∈ Icc 1 Q, f a)*(∑ b ∈ Icc 1 Q, g b) := by
  let S := Icc 1 Q
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have hw (p : ℕ × ℕ) : 0 ≤ w p := mul_nonneg (hf _) (hg _)
  have hsub (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal ⊆ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    intro ab hab
    have hm (d : ℕ) (hd : d ∈ q.divisors) : d ∈ S :=
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (mem_Icc.mp hq).1 (Nat.dvd_of_mem_divisors hd)).trans (mem_Icc.mp hq).2⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
      hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
  change (∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w p :=
      sum_le_sum fun q hq => sum_le_sum_of_subset_of_nonneg (hsub q hq) (fun p _ _ => hw p)
    _ = ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w p :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ S ×ˢ S, w p := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hw p)
    _ = (∑ a ∈ S, f a)*(∑ b ∈ S, g b) := by rw [sum_product, sum_mul_sum]
set_option maxHeartbeats 1000000 in

private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1/(q.totient:ℝ) ≤ Real.exp (2*squareMass) *
      ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  calc
    _ = ((q:ℝ)/(q.totient:ℝ))/q := by
      rw [div_right_comm, div_self hq'.ne']
    _ ≤ (Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹)/q :=
      div_le_div_of_nonneg_right (ratio_le_divisors q hq) hq'.le
    _ = _ := by
      rw [mul_div_assoc, Finset.sum_div,
        ← Nat.sum_divisorsAntidiagonal (fun d _ => (d:ℝ)⁻¹/q) (n := q)]
      congr 1
      refine sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul, div_eq_mul_inv,
        mul_inv, ← inv_pow, pow_two, mul_assoc]

set_option maxHeartbeats 1000000 in
/-- The sum of reciprocal totients costs one logarithm, uniformly in `Q`. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1/(q.totient:ℝ)) ≤ weightConstant * (1+Real.log Q) := by
  calc
    _ ≤ Real.exp (2*squareMass) * (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal,
        ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1
    _ ≤ Real.exp (2*squareMass) * ((∑ a ∈ Icc 1 Q, ((a:ℝ)^2)⁻¹)*(∑ b ∈ Icc 1 Q, (b:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (sum_antidiagonal_le_product Q (fun a => ((a:ℝ)^2)⁻¹) (fun b => (b:ℝ)⁻¹)
        (fun _ => by positivity) (fun _ => by positivity)) (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass*(1+Real.log Q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (sum_square_inv_le _) (harmonic_bound Q)
        (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := (mul_assoc ..).symm

set_option maxHeartbeats 1000000 in
/-- Conductor multiplicities lose a single logarithm, including `d = 1`. -/
theorem sum_conductor_weights (Q : ℕ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ q ∈ Icc 1 Q, (∑ d ∈ q.divisors, F d)/(q.totient:ℝ)) ≤
      (∑ d ∈ Icc 1 Q, F d/(d.totient:ℝ)) * (weightConstant*(1+Real.log Q)) := by
  let f (d : ℕ) := F d/(d.totient:ℝ)
  let g (m : ℕ) := 1/(m.totient:ℝ)
  have hf (d : ℕ) : 0 ≤ f d := div_nonneg (hF d) (Nat.cast_nonneg _)
  have hg (m : ℕ) : 0 ≤ g m := by dsimp [g]; positivity
  have hterm (q : ℕ) : (∑ d ∈ q.divisors, F d)/(q.totient:ℝ) ≤
      ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := by
    rw [Finset.sum_div, ← Nat.sum_divisorsAntidiagonal (fun d _ => F d/(q.totient:ℝ)) (n := q)]
    refine sum_le_sum fun p hp => ?_
    have h1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have h2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    have h3 : 0 < (p.1.totient:ℝ)*(p.2.totient:ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr h1) (Nat.totient_pos.mpr h2)
    have hφ := Nat.totient_super_multiplicative p.1 p.2
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1] at hφ
    calc
      _ ≤ F p.1/((p.1.totient:ℝ)*(p.2.totient:ℝ)) :=
        div_le_div_of_nonneg_left (hF _) h3 (by exact_mod_cast hφ)
      _ = _ := by
        simp only [f, g, div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := sum_le_sum fun q _ => hterm q
    _ ≤ (∑ d ∈ Icc 1 Q, f d)*(∑ m ∈ Icc 1 Q, g m) := sum_antidiagonal_le_product Q f g hf hg
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_totient_le Q) (sum_nonneg fun d _ => hf d)


end InnerFloorLinearTotient

end

end

/-! BEGIN InnerFloorPrimeWeightTransfer.lean; sha256 e0fe19fd388e2875008d291af7c349de679243e607af5bb0c94ebb053e00177e -/
section
/-!
Transfer from von Mangoldt windows to logarithmic prime windows, preserving
the character index and family squared-energy budget. This is independent
of zero-free assumptions and does not assert a bound on the zero sum.
-/

open Finset ArithmeticFunction MeasureTheory
open scoped Interval Classical
open OAI.Ostmann V7e V2h
namespace InnerFloorResearch
noncomputable section

def logPrimeWeight (k : ℕ) : ℝ :=
  if k.Prime then Real.log k else 0

theorem logPrimeWeight_le_vonMangoldt (k : ℕ) :
    logPrimeWeight k ≤ vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [logPrimeWeight,hk,vonMangoldt_apply_prime hk]
  · simp [logPrimeWeight,hk]

/-- An arbitrary bounded multiplier cannot amplify the total proper
prime-power mass on any subset of the prefix. -/
theorem weightedPrimePowerError (s : Finset ℕ) (X : ℝ)
    (hsub : s ⊆ Ioc 0 ⌊X⌋₊) (a : ℕ → ℂ)
    (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) :
    ‖(∑ k∈s, (vonMangoldt k:ℂ)*a k) -
      (∑ k∈s, (logPrimeWeight k:ℂ)*a k)‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  have htotal :
      (∑ k∈Ioc 0 ⌊X⌋₊, (vonMangoldt k-logPrimeWeight k)) =
        Chebyshev.psi X-Chebyshev.theta X := by
    simp only [sum_sub_distrib,Chebyshev.psi,Chebyshev.theta,sum_filter,logPrimeWeight]
  rw [← sum_sub_distrib,← htotal]
  calc
    _ ≤ ∑ k∈s, ‖(vonMangoldt k:ℂ)*a k-(logPrimeWeight k:ℂ)*a k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k∈s, (vonMangoldt k-logPrimeWeight k) := by
      apply sum_le_sum
      intro k hk
      rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k))]
      exact mul_le_of_le_one_right (sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k)) (ha k hk)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k))

/-- Exact identification of the floor-based integer-length window. -/
theorem windowIndices_eq (y : ℝ) (h : ℕ) (hy : 0 ≤ y) :
    V9a h y = Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
  rw [V9a,Nat.floor_add_natCast hy h]
  ext k
  simp only [mem_Ioc,mem_Icc,Nat.add_one_le_iff]

theorem centeredPrimeWindowError (χ : PrimitiveComplexCharacter)
    {X y : ℝ} (h : ℕ) (hy : 0 ≤ y) (hX : y+(h:ℝ) ≤ X) :
    ‖V4q χ h y - InnerFloorAP.centeredPrimeSum χ.character y h‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  let s := V9a h y
  have hsub : s ⊆ Ioc 0 ⌊X⌋₊ := by
    intro k hk
    have hm : k∈Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
      simpa only [s,windowIndices_eq y h hy] using hk
    have hk' := (InnerFloorAP.mem_window hy (Nat.cast_nonneg h) k).mp hm
    exact mem_Ioc.mpr ⟨by exact_mod_cast hy.trans_lt hk'.1,
      (Nat.le_floor_iff (by linarith [Nat.cast_nonneg (α := ℝ) h])).2 (hk'.2.trans hX)⟩
  have he := weightedPrimePowerError s X hsub
    (fun k => χ.character (k:ZMod χ.modulus))
    (fun k _ => DirichletCharacter.norm_le_one _ _)
  unfold V4q InnerFloorAP.centeredPrimeSum
  rw [if_neg χ.nontrivial,sub_zero,← windowIndices_eq y h hy]
  simp only [Vl,mul_comm (χ.character _),logPrimeWeight] at he ⊢
  exact he

/-- The family error is at most O(Q² X² log² X) on [X,2X],
using the uniform proper-prime-power mass bound and the primitive
character cardinality estimate. -/
theorem primitivePrimeWindowErrorEnergy (F : Finset PrimitiveComplexCharacter)
    (Q h : ℕ) {X : ℝ} (hX : 1≤X) (hh : (h:ℝ)≤X)
    (hF : ∀ χ∈F, χ.modulus≤Q) :
    (∑ χ∈F, ∫ y in X..2*X,
      ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
      X*(Q:ℝ)^2*(2*Real.sqrt (3*X)*Real.log (3*X))^2 := by
  let M := 2*Real.sqrt (3*X)*Real.log (3*X)
  have hM : 0≤M := by
    have hl : 0≤Real.log (3*X) := Real.log_nonneg (by linarith)
    dsimp [M]
    positivity
  have hterm (χ : PrimitiveComplexCharacter) :
      (∫ y in X..2*X, ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        X*M^2 := by
    have hXX : X≤2*X := by linarith
    rw [intervalIntegral.integral_of_le hXX]
    have hb : ∀ y∈Set.Ioc X (2*X),
        ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2≤M^2 := by
      intro y hy
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      exact (centeredPrimeWindowError χ h (by linarith [hy.1])
        (by linarith [hy.2])).trans (Chebyshev.psi_sub_theta_le (by linarith))
    calc
      _ ≤ ∫ _y in Set.Ioc X (2*X), M^2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
          (integrableOn_const (by simp)) (by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
            exact hb y hy)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hXX,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  calc
    _ ≤ ∑ _χ∈F, X*M^2 := sum_le_sum fun χ _ => hterm χ
    _ = (F.card:ℝ)*(X*M^2) := by simp [nsmul_eq_mul]
    _ ≤ _ := by
      have hc : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
      have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0≤X*M^2)
      dsimp [M] at *
      nlinarith only [hm]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorReducedGaussEnergy.lean; sha256 5679806f7783b3070a00d5c314d56348a3222f63907d83a536c10ec2a3d0ac68 -/
section
/-!
Research-only reduced-numerator projection for the inner-remainder problem.
Unlike the full additive Parseval bound (which pays q for every character),
this theorem pays the conductor of each character. It is an exact finite
identity followed by the already verified conductor-sensitive Gauss bound.
No prime distribution assumption is included.
-/

open Finset
open scoped Classical
namespace InnerFloorResearch
noncomputable section

variable {q : ℕ} [NeZero q]

open DyadicMixedB4RamanujanCharacters
open DyadicMixedB4CharacterFactorBound
open Conjectures.Goldbach.ReflectionCharacterContraction_aux

def unitAdditiveError (b : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  ∑ r : (ZMod q)ˣ, b r * ZMod.stdAddChar ((a : ZMod q) * (r : ZMod q))

def unitCharacterError (b : (ZMod q)ˣ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ r : (ZMod q)ˣ, b r * χ (r : ZMod q)

theorem reducedSynthesis (b : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    unitAdditiveError b a =
      ∑ χ : DirichletCharacter ℂ q,
        (gaussSum χ⁻¹ ZMod.stdAddChar * unitCharacterError b χ /
          (q.totient : ℂ)) * χ (a : ZMod q) := by
  have hExp (r : (ZMod q)ˣ) :
      ZMod.stdAddChar ((a : ZMod q) * (r : ZMod q)) =
        (∑ χ : DirichletCharacter ℂ q,
          (χ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) *
            χ (a : ZMod q)) / (q.totient : ℂ) := by
    have hFintype :
        DyadicMixedB4RamanujanCharacters.unitFintype q =
          (inferInstance : Fintype (ZMod q)ˣ) := Subsingleton.elim _ _
    have h := unit_character_expansion
      (fun x : (ZMod q)ˣ => ZMod.stdAddChar ((x : ZMod q) * (r : ZMod q))) a
    rw [hFintype] at h
    have ht (χ : DirichletCharacter ℂ q) :
        (∑ x : (ZMod q)ˣ, star (χ (x : ZMod q)) *
          ZMod.stdAddChar ((x : ZMod q) * (r : ZMod q))) =
          χ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
      have h' := unit_twisted_gauss χ (1 : (ZMod q)ˣ) r
      rw [hFintype] at h'
      simpa only [Units.val_one, one_mul, map_one] using h' 
    simpa only [ht] using h
  unfold unitAdditiveError
  simp_rw [hExp, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  unfold unitCharacterError
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem reducedGaussEnergy (b : (ZMod q)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖unitAdditiveError b a‖^2) =
      (∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖^2 * ‖unitCharacterError b χ‖^2) /
        (q.totient : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  simp_rw [reducedSynthesis]
  rw [synth_norm]
  simp only [norm_div, norm_mul, Complex.norm_natCast, Nat.cast_ofNat, mul_pow]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro χ _
  field_simp

theorem reducedConductorEnergy (b : (ZMod q)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖unitAdditiveError b a‖^2) ≤
      (∑ χ : DirichletCharacter ℂ q,
        (χ.conductor : ℝ) * ‖unitCharacterError b χ‖^2) /
        (q.totient : ℝ) := by
  rw [reducedGaussEnergy]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro χ _
  have hg := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at hg
  have hs := pow_le_pow_left₀ (norm_nonneg _) hg 2
  rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hs
  exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorConductorLift.lean; sha256 5d27e5673abcc38957a96f379096c1f778d2d2ff05f0f7b98b5ef127f81197d3 -/
section
/-!
Reduced-numerator conductor aggregation. This is an auxiliary research
statement and does not assume or assert the unproved primitive mean square.
The accepted ShortProgressionsMeanTheta module supplies the exact conductor
lifting for interior prime windows and the reciprocal-totient estimates.
-/

open Finset
open scoped Classical
namespace InnerFloorResearch
noncomputable section

open BombieriVinogradov.LargeSieve
open DyadicMixedB4ConductorPartition
open Conjectures.Goldbach.ReflectionCharacterContraction_aux

def reducedLevelEnergy (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : (ZMod q)ˣ, ‖unitAdditiveError (b q) a‖^2

/-- Only logarithmic conductor multiplicity is paid in the reduced projection.
F d is an arbitrary primitive-family energy budget. -/
theorem reducedFamilyEnergy (A : ℕ)
    (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d)
    (hcompat : ∀ (q : ℕ) [NeZero q], q ≤ A →
      ∀ (d : ℕ) (hd : d ∣ q),
        (∑ ψ ∈ primitiveCharacters d,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2) ≤ F d) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy b q) ≤
      (∑ d ∈ Icc 1 A, (d : ℝ)*F d/(d.totient : ℝ)) *
        (InnerFloorLinearTotient.weightConstant*(1+Real.log A)) := by
  have hterm (q : ℕ) (hq : q ∈ Icc 1 A) :
      reducedLevelEnergy b q ≤ (∑ d ∈ q.divisors, (d : ℝ)*F d)/(q.totient : ℝ) := by
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0.ne'⟩
    simp only [reducedLevelEnergy, dif_neg hq0.ne']
    apply (reducedConductorEnergy (b q)).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [sum_conductor_partition]
    rw [← Finset.sum_attach q.divisors (fun d => (d : ℝ)*F d)]
    apply sum_le_sum
    intro d _
    have hd : d.1 ∣ q := (Nat.mem_divisors.mp d.2).1
    calc
      _ = (d.1 : ℝ) * ∑ ψ ∈ primitiveCharacters d.1,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2 := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro ψ hψ
        have hp : ψ.IsPrimitive := (mem_filter.mp hψ).2
        rw [(DirichletCharacter.conductor_changeLevel ψ hd).trans hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcompat q (mem_Icc.mp hq).2 d.1 hd)
        (Nat.cast_nonneg _)
  exact (sum_le_sum hterm).trans
    (InnerFloorLinearTotient.sum_conductor_weights A (fun d => (d : ℝ)*F d)
      (fun d => mul_nonneg (Nat.cast_nonneg _) (hF d)))

/-- Two logarithms, rather than a polynomial factor in A, suffice to lift
a primitive squared-error budget to reduced-numerator energy. -/
theorem reducedFamilyEnergyLog (A : ℕ)
    (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d)
    (hcompat : ∀ (q : ℕ) [NeZero q], q ≤ A →
      ∀ (d : ℕ) (hd : d ∣ q),
        (∑ ψ ∈ primitiveCharacters d,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2) ≤ F d) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy b q) ≤
      (InnerFloorLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d ∈ Icc 1 A, F d := by
  let W := InnerFloorLinearTotient.weightConstant
  let L := 1 + Real.log A
  have hW : 0 ≤ W := InnerFloorLinearTotient.weightConstant_nonneg
  have hL : 0 ≤ L := by
    dsimp [L]
    linarith [Real.log_natCast_nonneg A]
  have hs : (∑ d ∈ Icc 1 A, (d : ℝ)*F d/(d.totient : ℝ)) ≤
      (W*L)*(∑ d ∈ Icc 1 A, F d) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have h := InnerFloorLinearTotient.ratio_totient_le d (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdA : (d : ℝ) ≤ A := by exact_mod_cast (mem_Icc.mp hd).2
    have hl := Real.log_le_log hd0 hdA
    have h' : (d : ℝ)/(d.totient : ℝ) ≤ W*L :=
      h.trans (mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) hW)
    calc
      _ = ((d : ℝ)/(d.totient : ℝ))*F d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h' (hF d)
  calc
    _ ≤ _ := reducedFamilyEnergy A b F hF hcompat
    _ ≤ ((W*L)*(∑ d ∈ Icc 1 A, F d))*(W*L) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg hW hL)
    _ = _ := by dsimp [W,L]; ring

def primeWindowResidueError (q : ℕ) (y h : ℝ) (r : (ZMod q)ˣ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (InnerFloorAP.theta q (r : ZMod q) y h : ℂ) -
      ((h/(q.totient : ℝ) : ℝ) : ℂ)

theorem primeWindowCharacterError {q : ℕ} [NeZero q] (y h : ℝ)
    (χ : DirichletCharacter ℂ q) :
    unitCharacterError (primeWindowResidueError q y h) χ =
      InnerFloorAP.centeredPrimeSum χ y h := by
  classical
  unfold unitCharacterError InnerFloorAP.centeredPrimeSum
  simp only [primeWindowResidueError, dif_neg (NeZero.ne q), sub_mul, sum_sub_distrib]
  congr 1
  · rw [sum_units_eq_sum
      (fun r : ZMod q => (InnerFloorAP.theta q r y h : ℂ)*χ r)
      (fun r hr => by rw [MulChar.map_nonunit χ hr, mul_zero])]
    simp only [InnerFloorAP.theta, Complex.ofReal_sum, sum_filter, apply_ite,
      Complex.ofReal_zero, sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    simp
  · rw [← Finset.mul_sum, sum_char_units]
    by_cases hc : χ = 1
    · rw [if_pos hc, if_pos hc]
      push_cast
      have hφ : (q.totient : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
      field_simp
    · simp [hc]

def primitivePrimeWindowEnergy (d : ℕ) (y h : ℝ) : ℝ :=
  ∑ ψ ∈ primitiveCharacters d, ‖InnerFloorAP.centeredPrimeSum ψ y h‖^2

theorem primeWindowReducedFamilyEnergy (A : ℕ) (y h : ℝ)
    (hy : (A : ℝ) ≤ y) (hh : 0 ≤ h) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy
      (fun q r => primeWindowResidueError q y h r) q) ≤
      (InnerFloorLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d ∈ Icc 1 A, primitivePrimeWindowEnergy d y h := by
  apply reducedFamilyEnergyLog
  · intro d
    exact sum_nonneg fun _ _ => sq_nonneg _
  · intro q inst hq d hd
    have hqy : (q : ℝ) ≤ y := (by exact_mod_cast hq : (q : ℝ) ≤ A).trans hy
    simp only [primeWindowCharacterError, InnerFloorAP.centeredPrimeSum_changeLevel hd _ hqy hh,
      primitivePrimeWindowEnergy, le_refl]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPrimitiveFamilyBridge.lean; sha256 738e1cd5a79c2cd3f5bfb922a80dff3823f5d9aa669c17e355aae5560c979b8d -/
section
/-!
The analytic family of nonprincipal primitive characters is exactly the
arithmetic family filtered by nontriviality. Modulus one is accounted
for separately. No density assumption occurs in this finite identity.
-/
open Finset BombieriVinogradov.LargeSieve
open OAI.Ostmann
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def indexedNonprincipal (A : ℕ) : Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Icc 1 A).sigma (fun q => (primitiveCharacters q).filter (fun χ => χ ≠ 1))

def analyticFamilyEmbedding (A : ℕ) :
    {p // p ∈ indexedNonprincipal A} ↪ PrimitiveComplexCharacter where
  toFun p :=
    let hp := Finset.mem_sigma.mp p.property
    let hc := Finset.mem_filter.mp hp.2
    ⟨p.val.1, (Finset.mem_Icc.mp hp.1).1, p.val.2,
      (Finset.mem_filter.mp hc.1).2, hc.2⟩
  inj' := by
    intro p r h
    apply Subtype.ext
    exact congrArg (fun χ : PrimitiveComplexCharacter =>
      (⟨χ.modulus, χ.character⟩ : Σ q : ℕ, DirichletCharacter ℂ q)) h

def analyticPrimitiveFamily (A : ℕ) : Finset PrimitiveComplexCharacter :=
  (indexedNonprincipal A).attach.map (analyticFamilyEmbedding A)

theorem analyticPrimitiveFamily_modulus (A : ℕ) :
    ∀ χ∈analyticPrimitiveFamily A, χ.modulus≤A := by
  intro χ hχ
  obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hχ
  exact (Finset.mem_Icc.mp (Finset.mem_sigma.mp p.property).1).2

theorem sum_analyticPrimitiveFamily (A : ℕ)
    (g : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    (∑ χ∈analyticPrimitiveFamily A,g χ.modulus χ.character) =
      ∑ q∈Icc 1 A, ∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1), g q χ := by
  unfold analyticPrimitiveFamily
  rw [Finset.sum_map]
  change (∑ p∈(indexedNonprincipal A).attach,g p.val.1 p.val.2) = _
  calc
    _ = ∑ p∈indexedNonprincipal A,g p.1 p.2 :=
      Finset.sum_attach (indexedNonprincipal A) (fun p => g p.1 p.2)
    _ = _ := by
      unfold indexedNonprincipal
      rw [Finset.sum_sigma]

/-- On every window, the primitive arithmetic energy is the sum of the
nonprincipal analytic family plus at most the single modulus-one term. -/
theorem primitiveEnergy_le_analyticFamily (A : ℕ) (y h : ℝ) :
    (∑ q∈Icc 1 A,primitivePrimeWindowEnergy q y h) ≤
      (∑ χ∈analyticPrimitiveFamily A,
        ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
      ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖^2 := by
  let g (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    ‖InnerFloorAP.centeredPrimeSum χ y h‖^2
  let P := ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖^2
  rw [sum_analyticPrimitiveFamily A g]
  have ht (q : ℕ) (hq : q∈Icc 1 A) :
      primitivePrimeWindowEnergy q y h ≤
        (∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) +
          (if q=1 then P else 0) := by
    change (∑ ψ∈primitiveCharacters q,g q ψ) ≤ _
    by_cases hmem : (1:DirichletCharacter ℂ q) ∈ primitiveCharacters q
    · have hprim : (1:DirichletCharacter ℂ q).IsPrimitive := (mem_filter.mp hmem).2
      have hq1 : q=1 := by
        letI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
        simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hprim.symm
      have he : (primitiveCharacters q).filter (fun χ => χ ≠ 1) =
          (primitiveCharacters q).erase 1 := by ext χ; simp [and_comm]
      rw [if_pos hq1,he]
      have hgP : g q (1:DirichletCharacter ℂ q) = P := by
        subst q
        rfl
      calc
        _ = (∑ χ∈(primitiveCharacters q).erase 1,g q χ)+g q 1 :=
          (sum_erase_add _ _ hmem).symm
        _ = _ := by rw [hgP]
      all_goals first | exact le_rfl | (apply le_of_eq; congr 1; apply sum_congr; · ext x; simp; · intros; rfl)
    · have he : (primitiveCharacters q).filter (fun χ => χ ≠ 1) =
          primitiveCharacters q := by
        ext χ
        simp only [mem_filter]
        exact ⟨fun h => h.1,fun h => ⟨h,fun hc => hmem (hc ▸ h)⟩⟩
      have hsum : (∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) =
          ∑ χ∈primitiveCharacters q,g q χ :=
        congrArg (fun S : Finset (DirichletCharacter ℂ q) => ∑ χ∈S,g q χ) he
      rw [hsum]
      apply le_add_of_nonneg_right
      split_ifs <;> positivity
  calc
    _ ≤ ∑ q∈Icc 1 A,
      ((∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) +
        (if q=1 then P else 0)) := sum_le_sum ht
    _ = (∑ q∈Icc 1 A, ∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) +
        (∑ q∈Icc 1 A, if q=1 then P else 0) := sum_add_distrib
    _ ≤ _ := by
      apply add_le_add_right
      rw [sum_ite_eq']
      split_ifs <;> first | exact le_rfl | exact sq_nonneg _

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPrincipalWindow.lean; sha256 27dbb0571fc97283db7ad41c190ca6b5436d42d13f9ec98a5cc79a80c1cf3347 -/
section
/-!
Unconditional principal short-window estimate retaining logarithmic
saving rather than collapsing the bound to h/4. Adapted from the
accepted DyadicCellShortPrimeFloor, actual_principal_window_of_zero_weights,
pinned upstream 1fe24b28. No extra zero-free hypothesis.
-/
open Finset Filter
open scoped BigOperators Classical Topology
open OAI.Ostmann GoldbachOC103 Vx V7e V86 V1e V6i
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem principalWindowLogFour :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(4/5 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ C*(h : ℝ)/(Real.log X)^4 := by
  have hzero := actual_zero_weight_bounds
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets D C C hD.le
  obtain ⟨Xp,hXp⟩ := eventually_atTop.mp
    (eventually_power_log_bound (3/4) (4/5) 1 1 4 (by norm_num) (by norm_num))
  refine ⟨2*C+1,by positivity,max Xz (max Xb Xp),?_⟩
  intro X hX h hlower hupper
  have hbud := hb X ((le_max_left Xb Xp).trans ((le_max_right _ _).trans hX))
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hX) hX4
    hbud.log_ge_one hbud.split_ge_two hbud.split_le_scale
  let S := V3b X
  let A := S.filter (fun c => |c.val.1.im| ≤ X^(5/16 : ℝ))
  let R := S.filter (fun c => ¬ |c.val.1.im| ≤ X^(5/16 : ℝ))
  let K := C*(Real.log X)^14/(X^(5/16 : ℝ)*Real.sqrt (X^(5/16 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : ∀ c ∈ S, |c.val.1.im| ≤ X := by
    intro c hc
    exact (V5l X c).mp hc
  have hlow : (∑ c ∈ A, X^(c.val.1.re-1)) ≤ C/(Real.log X)^4 :=
    hlo A (fun c hc => (mem_filter.mp hc).2)
  have hhigh : ∀ v : ℝ, X^(5/16 : ℝ) ≤ v →
      (∑ c ∈ R.filter (fun c => |c.val.1.im| ≤ v), X^(c.val.1.re-1)) ≤
        K*v*Real.sqrt v := by
    intro v hv
    exact weight_count_clamp R X (X^(5/16 : ℝ)) K v hV hbud.split_le_scale hK hv
      (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := smoothed_packet_of_weight_bounds S (fun c => c.val.1)
    X X h (X^(2/3 : ℝ)) (X^(5/16 : ℝ)) (C/(Real.log X)^4) K
    (by linarith) le_rfl (by linarith) hh hupper hδ hbud.smoothing_le_half hV hK
    (fun c _ => c.property.1.1) (fun c _ => c.property.1.2.1.le) hlow hhigh
  have hHighBudget :
      576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
        X^(3/4 : ℝ)/16 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    exact hbud.high_budget
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ X^(3/4 : ℝ)/16 := by
    exact hres.trans hbud.residual_budget
  have hnorm : ‖V42 h X‖ ≤
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ +
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
        (V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
  have hsmall := (hXp X ((le_max_right Xb Xp).trans ((le_max_right _ _).trans hX))).2
  have hlogp : 0 < Real.log X := by linarith [hbud.log_ge_one]
  have hsmall' : X^(3/4 : ℝ) ≤ (h:ℝ)/(Real.log X)^4 := by
    apply (le_div_iff₀ (pow_pos hlogp 4)).2
    have hs : X^(3/4 : ℝ)*(Real.log X)^4 ≤ X^(4/5 : ℝ) := by
      simpa only [one_mul] using hsmall
    exact hs.trans hlower
  calc
    _ ≤ X^(3/4 : ℝ)/16 +
      (2*(h:ℝ)*(C/(Real.log X)^4)+X^(3/4 : ℝ)/16) :=
      hnorm.trans (add_le_add hResidualBudget (hpacket.trans
        (add_le_add_right hHighBudget _)))
    _ ≤ _ := by
      linarith only [hsmall',div_nonneg hh (pow_nonneg hlogp.le 4),
        show (2*C+1)*(h:ℝ)/(Real.log X)^4 =
          2*(h:ℝ)*(C/(Real.log X)^4)+(h:ℝ)/(Real.log X)^4 by ring]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPrincipalPrimeWindow.lean; sha256 fac11ade5d656d636f05f28b9ae22c21c091dfb6656ad7e502ba470d8908202d -/
section
/-! Principal prime window, without the nonprincipal zero-strip input. -/
open Finset Filter ArithmeticFunction
open scoped Classical Topology
open OAI.Ostmann V7e V2h GoldbachOC103
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem principalPrimePowerWindowError (χ : DirichletCharacter ℂ 1)
    {X y : ℝ} (h : ℕ) (hy : 0 ≤ y) (hX : y+(h:ℝ) ≤ X) :
    ‖V42 h y - InnerFloorAP.centeredPrimeSum χ y h‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  have hχ : χ=1 := by
    ext1 r
    rw [show r=1 from Subsingleton.elim _ _]
    simp
  subst χ
  let s := V9a h y
  have hsub : s ⊆ Ioc 0 ⌊X⌋₊ := by
    intro k hk
    have hm : k∈Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
      simpa only [s,windowIndices_eq y h hy] using hk
    have hk' := (InnerFloorAP.mem_window hy (Nat.cast_nonneg h) k).mp hm
    exact mem_Ioc.mpr ⟨by exact_mod_cast hy.trans_lt hk'.1,
      (Nat.le_floor_iff (by linarith [Nat.cast_nonneg (α := ℝ) h])).2 (hk'.2.trans hX)⟩
  have he := weightedPrimePowerError s X hsub (fun _ => 1) (by simp)
  have hval (k : ℕ) : (1 : DirichletCharacter ℂ 1) (k:ZMod 1)=1 := by
    rw [show (k:ZMod 1)=1 from Subsingleton.elim _ _]
    simp
  unfold V42 InnerFloorAP.centeredPrimeSum
  rw [if_pos rfl,← windowIndices_eq y h hy]
  simp only [hval,mul_one,V1n]
  rw [show ((h:ℝ):ℂ)=(h:ℂ) by norm_cast, sub_sub_sub_cancel_right]
  simpa only [s,mul_one,logPrimeWeight] using he

theorem principalPrimeWindowLogFour :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(4/5:ℝ) ≤ (h:ℝ) → (h:ℝ) ≤ X → ∀ χ : DirichletCharacter ℂ 1,
      ‖InnerFloorAP.centeredPrimeSum χ X h‖ ≤ C*(h:ℝ)/(Real.log X)^4 := by
  obtain ⟨C,hC,X₁,h₁⟩ := principalWindowLogFour
  obtain ⟨X₂,h₂⟩ := eventually_atTop.mp
    (eventually_power_log_bound (1/2) (4/5) 8 1 5 (by norm_num) (by norm_num))
  refine ⟨C+1,by positivity,max 2 (max X₁ X₂),le_max_left ..,?_⟩
  intro X hX h hh hhX χ
  have hX2 : 2≤X := (le_max_left _ _).trans hX
  have hX1 : X₁≤X := (le_max_left X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hX₂ : X₂≤X := (le_max_right X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog : Real.log (2*X) ≤ 2*Real.log X := by
    rw [Real.log_mul (by norm_num) hXp.ne']
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 2) hX2]
  have hsqrt : Real.sqrt (2*X) ≤ 2*Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ 2) (Real.sqrt_nonneg _)
  have hpow := (h₂ X hX₂).2
  have hsmall : 8*Real.sqrt X*Real.log X ≤ (h:ℝ)/(Real.log X)^4 := by
    apply (le_div_iff₀ (pow_pos hL 4)).2
    calc
      _ = 8*X^(1/2:ℝ)*(Real.log X)^5 := by rw [Real.sqrt_eq_rpow]; ring
      _ ≤ _ := (by simpa only [one_mul] using hpow : 8*X^(1/2:ℝ)*(Real.log X)^5 ≤ X^(4/5:ℝ)).trans hh
  have herr := principalPrimePowerWindowError χ (X := 2*X) h hXp.le (by linarith)
  have herror : ‖V42 h X-InnerFloorAP.centeredPrimeSum χ X h‖ ≤ (h:ℝ)/(Real.log X)^4 := by
    apply herr.trans
    apply (Chebyshev.psi_sub_theta_le (by linarith : 1 ≤ 2*X)).trans
    calc
      _ ≤ 2*(2*Real.sqrt X)*(2*Real.log X) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        · exact hlog
        · exact Real.log_nonneg (by linarith)
        · positivity
      _ = 8*Real.sqrt X*Real.log X := by ring
      _ ≤ _ := hsmall
  have hnorm := norm_sub_le (V42 h X) (V42 h X-InnerFloorAP.centeredPrimeSum χ X h)
  rw [sub_sub_cancel] at hnorm
  calc
    _ ≤ _ := hnorm
    _ ≤ C*(h:ℝ)/(Real.log X)^4+(h:ℝ)/(Real.log X)^4 :=
      add_le_add (h₁ X hX1 h hh hhX) herror
    _ = _ := by ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorReducedGallagher.lean; sha256 c8ab1eb19cb343c545fe2dc706e54933e69ea9bd4d75727892e88888c0803b6e -/
section
/-!
Reduced-numerator Gallagher reduction. Unlike GBSkirtVariance.denominator_bound
this never sums over the nonunit numerators and never relaxes to q times the
full residue variance. The exact interior window is identified with the
verified conductor-lift estimate. The clipped endpoint windows are separate.
-/

open Finset MeasureTheory
open scoped Interval Classical
open GoldbachWindow (poly moving)
open GoldbachGRHAnalytic (errorCoeff)
open GoldbachGRHWindow (primeLog)
open Conjectures.Goldbach.ReflectionCharacterContraction_aux
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem reducedDenominatorBound {q : ℕ} [NeZero q] (n h : ℕ)
    (δ : ℝ) (hh : 0<h) (hd : 0≤δ) (hw : 6*(h:ℝ)*δ≤1) :
    (h:ℝ)^2/4 * (∑ a : (ZMod q)ˣ,
      ∫ t in -δ..δ, ‖poly (n+1) (errorCoeff (a:ZMod q)) t‖^2) ≤
      ∑ m∈range (n+1+h), ∑ a : (ZMod q)ˣ,
        ‖moving (n+1) h (errorCoeff (a:ZMod q)) m‖^2 := by
  rw [Finset.mul_sum,Finset.sum_comm (s := range (n+1+h))]
  exact sum_le_sum fun a _ =>
    GoldbachWindow.low_frequency_le (n+1) h (errorCoeff (a:ZMod q)) δ hh hd hw

theorem interiorWindowIndices (n y h : ℕ) (hfull : y+h≤n) :
    GBSkirtVariance.window n h (y+h) = Icc (y+1) (y+h) := by
  unfold GBSkirtVariance.window
  rw [min_eq_left hfull,show y+h+1-h=y+1 by omega]

theorem interiorResidueError_eq_zero {q : ℕ} [NeZero q]
    (n y h : ℕ) (hqy : q≤y) (hfull : y+h≤n)
    (r : ZMod q) (hr : ¬IsUnit r) :
    GBSkirtVariance.residueError (GBSkirtVariance.window n h (y+h)) primeLog r = 0 := by
  rw [interiorWindowIndices n y h hfull]
  unfold GBSkirtVariance.residueError
  rw [if_neg hr,sub_zero]
  change (∑ k ∈ (Icc (y+1) (y+h)).filter (fun k : ℕ => (k:ZMod q)=r),
    primeLog k)=0
  apply sum_eq_zero
  intro k hk
  obtain ⟨hk',hkr⟩ := mem_filter.mp hk
  have hqk : q<k := by have := (mem_Icc.mp hk').1; omega
  have hnp : ¬k.Prime := by
    intro hp
    have hcop : k.Coprime q := hp.coprime_iff_not_dvd.mpr
      (fun hd => (Nat.not_le_of_gt hqk) (Nat.le_of_dvd (NeZero.pos q) hd))
    exact hr (hkr ▸ (ZMod.isUnit_iff_coprime k q).mpr hcop)
  simp [primeLog,hnp]

theorem interiorResidueError_eq {q : ℕ} [NeZero q] (n y h : ℕ)
    (hfull : y+h≤n) (r : (ZMod q)ˣ) :
    GBSkirtVariance.residueError (GBSkirtVariance.window n h (y+h))
      primeLog (r:ZMod q) = primeWindowResidueError q y h r := by
  rw [interiorWindowIndices n y h hfull]
  unfold GBSkirtVariance.residueError
  change (∑ k ∈ (Icc (y+1) (y+h)).filter (fun k : ℕ => (k:ZMod q)=(r:ZMod q)),
    primeLog k) - (if IsUnit (r:ZMod q) then
      ((Icc (y+1) (y+h)).card:ℂ)/(q.totient:ℂ) else 0) =
    primeWindowResidueError q y h r
  simp only [r.isUnit,if_pos,primeWindowResidueError,dif_neg (NeZero.ne q),
    InnerFloorAP.theta,← Nat.cast_add,Nat.floor_natCast,Complex.ofReal_sum,
    Complex.ofReal_div,Complex.ofReal_natCast,primeLog]
  congr 1
  have hc : (Icc (y+1) (y+h)).card=h := by rw [Nat.card_Icc]; omega
  rw [hc]

theorem interiorMoving_eq_reduced {q : ℕ} [NeZero q] (n y h : ℕ)
    (hqy : q≤y) (hfull : y+h≤n) (a : (ZMod q)ˣ) :
    moving (n+1) h (errorCoeff (a:ZMod q)) (y+h) =
      unitAdditiveError (primeWindowResidueError q y h) a := by
  rw [GBSkirtVariance.moving_fourier]
  unfold unitAdditiveError
  rw [← sum_units_eq_sum
    (fun r : ZMod q => GBSkirtVariance.residueError
      (GBSkirtVariance.window n h (y+h)) primeLog r *
      ZMod.stdAddChar ((a:ZMod q)*r))
    (fun r hr => by rw [interiorResidueError_eq_zero n y h hqy hfull r hr,zero_mul])]
  exact sum_congr rfl fun r _ => by rw [interiorResidueError_eq n y h hfull]

def reducedMovingLevelEnergy (q n h m : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : (ZMod q)ˣ, ‖moving (n+1) h (errorCoeff (a:ZMod q)) m‖^2

/-- Full interior windows over any bounded family of levels satisfy the
same logarithmic conductor-lifting bound. No additional q factor. -/
theorem interiorReducedMovingFamilyEnergy (A n y h : ℕ)
    (hAy : A≤y) (hfull : y+h≤n) :
    (∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h (y+h)) ≤
      (InnerFloorLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h := by
  calc
    _ = ∑ q∈Icc 1 A, reducedLevelEnergy
      (fun q r => primeWindowResidueError q y h r) q := by
      apply sum_congr rfl
      intro q hq
      have hq0 : q≠0 := by have := (mem_Icc.mp hq).1; omega
      letI : NeZero q := ⟨hq0⟩
      simp only [reducedMovingLevelEnergy,reducedLevelEnergy,dif_neg hq0]
      apply sum_congr rfl
      intro a _
      rw [interiorMoving_eq_reduced n y h ((mem_Icc.mp hq).2.trans hAy) hfull]
    _ ≤ _ := primeWindowReducedFamilyEnergy A y h
      (by exact_mod_cast hAy) (Nat.cast_nonneg h)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorDiscreteWindowEnergy.lean; sha256 50d3e37cefa18b2d53b7a302c5618238db4e07ff9bfe8f8e9849801575f47197 -/
section
/-!
Integer-to-real window energy without any inequality loss.
Generic step integral adapted from GBSkirtVariance.paper_integral,
accepted LowSkirtFromShortProgressions at pinned upstream 1fe24b28.
-/
open Finset MeasureTheory
open scoped Classical Interval
namespace InnerFloorResearch
noncomputable section

theorem centeredPrimeSum_on_unit {d : ℕ}
    (χ : DirichletCharacter ℂ d) (k h : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    InnerFloorAP.centeredPrimeSum χ y h =
      InnerFloorAP.centeredPrimeSum χ (k:ℝ) h := by
  have hy₀ := (Nat.cast_nonneg k (α:=ℝ)).trans hy.1
  have hk : ⌊y⌋₊=k := (Nat.floor_eq_iff hy₀).2 ⟨hy.1,by simpa using hy.2⟩
  simp only [InnerFloorAP.centeredPrimeSum,Nat.floor_add_natCast hy₀,
    hk,Nat.floor_natCast,Nat.floor_add_natCast (Nat.cast_nonneg (α:=ℝ) k)]

theorem primitivePrimeWindowEnergy_on_unit (d k h : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    primitivePrimeWindowEnergy d y h = primitivePrimeWindowEnergy d k h := by
  unfold primitivePrimeWindowEnergy
  apply sum_congr rfl
  intro χ _
  rw [centeredPrimeSum_on_unit χ k h hy]

theorem integer_step_integral (x z : ℕ) (hxz : x≤z)
    (f : ℝ → ℝ) (g : ℕ → ℝ)
    (hstep : ∀ k : ℕ, ∀ y∈Set.Ico (k:ℝ) ((k+1:ℕ):ℝ), f y=g k) :
    (∫ y in (x:ℝ)..(z:ℝ), f y) = ∑ k∈Ico x z,g k := by
  let a (k : ℕ) := (k:ℝ)
  have hle (k : ℕ) : a k ≤ a (k+1) := by dsimp [a]; push_cast; linarith
  have hi (k : ℕ) : IntervalIntegrable f volume (a k) (a (k+1)) := by
    apply (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).2
    have hc : IntegrableOn (fun _ : ℝ => g k) (Set.Ico (a k) (a (k+1))) volume :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).1 intervalIntegrable_const
    apply hc.congr_fun _ measurableSet_Ico
    intro y hy
    exact (hstep k y hy).symm
  have he (k : ℕ) : (∫ y in a k..a (k+1), f y) = g k := by
    rw [intervalIntegral.integral_of_le (hle k), ← integral_Ico_eq_integral_Ioc]
    calc
      _ = ∫ _y in Set.Ico (a k) (a (k+1)), g k := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro y hy
        exact hstep k y hy
      _ = _ := by simp [a,Real.volume_Ico]
  have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico (a:=a) (m:=x) (n:=z)
    hxz (fun k _ => hi k)
  exact ht.symm.trans (sum_congr rfl fun k _ => he k)

theorem primitiveFamilyIntegerEnergy (A h x z : ℕ) (hxz : x≤z) :
    (∑ k∈Ico x z, ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d k h) =
      ∫ y in (x:ℝ)..(z:ℝ), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h := by
  symm
  apply integer_step_integral x z hxz
  intro k y hy
  exact sum_congr rfl fun d _ => primitivePrimeWindowEnergy_on_unit d k h hy

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGoodZeroWindow.lean; sha256 04947e34415b17372c0c133c87734bab40ed9812a6908529513fca7a6862e34a -/
section
/-!
Research auxiliary: the accepted primitive-character zero-density mean-square
estimate applies to the entire fixed-strip part of the zero spectrum on the
inner-arc window scale. This does NOT assert that the remaining zero spectrum
is empty, and does NOT assume or import GRH.
-/

open Finset Filter MeasureTheory
open scoped Interval Topology Classical
open OAI.Ostmann V1l V1e Vg2
namespace InnerFloorResearch
noncomputable section

/-- A fixed strip gap eventually dominates the logarithmic cutoff of the
existing zero-density estimate. -/
theorem fixedStripDominatesCutoff (B : ℕ) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, V2j (B+4) X ≤ (1/8 : ℝ) := by
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X)/Real.log X)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have h := (tendsto_const_nhds (x := (3 : ℝ)*((B+4+14 : ℕ) : ℝ))).mul ht
  have he := h.eventually (gt_mem_nhds (show
    (3 : ℝ)*((B+4+14 : ℕ) : ℝ)*0 < 1/8 by norm_num))
  have he' : ∀ᶠ X : ℝ in atTop, V2j (B+4) X ≤ (1/8 : ℝ) := by
    filter_upwards [he] with X hX
    have hX' : (3 : ℝ)*((B+4+14 : ℕ) : ℝ)*
        (Real.log (Real.log X)/Real.log X) < 1/8 := by simpa using hX
    unfold V2j
    rw [mul_div_assoc]
    exact hX'.le
  exact eventually_atTop.mp he'

/-- For the dyadic height band, the entire 1/2 <= beta <= 7/8 component
has a log-saving mean square. The family and zero subsets can vary freely. -/
theorem fixedStripWindowBand (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h T : ℝ,
      X₀≤X → 2≤T → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ ((V1 χ).V14 T).filter (fun i =>
        1/2≤((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re≤7/8 ∧
        T/2≤|((V1 χ).zeros i).im|)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,h₁⟩ := V93.Vz7 B
  obtain ⟨X₂,h₂⟩ := fixedStripDominatesCutoff B
  refine ⟨C,hC,max X₁ X₂,?_⟩
  intro Q hQ X h T hX hT hh hhX hscale hlog F hF S hS
  apply h₁ Q hQ X h T ((le_max_left _ _).trans hX) hT hh hhX
    hscale hlog F hF S
  intro χ hχ i hi
  obtain ⟨hiT,hiR,hiB,hiH⟩ := mem_filter.mp (hS χ hχ hi)
  have hc := h₂ X ((le_max_right _ _).trans hX)
  unfold Vy2
  exact mem_filter.mpr ⟨hiT,hiR,by linarith,hiH⟩

/-- At height <= 2, the same estimate holds, without a lower-height
restriction. -/
theorem fixedStripWindowLow (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h : ℝ,
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*2)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ ((V1 χ).V14 2).filter (fun i =>
        1/2≤((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re≤7/8)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,h₁⟩ := V93.V1ep B
  obtain ⟨X₂,h₂⟩ := fixedStripDominatesCutoff B
  refine ⟨C,hC,max X₁ X₂,?_⟩
  intro Q hQ X h hX hh hhX hscale hlog F hF S hS
  apply h₁ Q hQ X h ((le_max_left _ _).trans hX) hh hhX
    hscale hlog F hF S
  intro χ hχ i hi
  obtain ⟨hiT,hiR,hiB⟩ := mem_filter.mp (hS χ hχ hi)
  have hc := h₂ X ((le_max_right _ _).trans hX)
  exact mem_filter.mpr ⟨hiT,hiR,by linarith⟩

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGoodZeroAssembly.lean; sha256 c28ec698a44d44c1795cfcd12d1159b20b3c9dab91199d50100716aa63543ded -/
section
/-!
All-height, fixed-strip primitive-character window energy.
The near-one zeros are deliberately not discarded: the conclusions apply
to arbitrary subsets satisfying the stated real-part cutoff.
-/

open Finset Filter MeasureTheory
open scoped Interval Topology Classical
open OAI.Ostmann V1e V6b V6i
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def zeroWindow (χ : PrimitiveComplexCharacter) (S : Finset ℕ)
    (h y : ℝ) : ℂ :=
  ∑ i ∈ S, Ve y h ((V1 χ).zeros i)

/-- Sum all the dyadic bands in the strip 1/2 ≤ Re ρ ≤ 7/8.
The loss is at most (K+1)^2, for U=2^(K+1). -/
theorem rightStripAllHeights (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ),
      1 ≤ Q → X₀ ≤ X → 0 < h → h ≤ X →
      (Q : ℝ)^2/(h/X) ≤ X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1)) ≤ 2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ ∈ F, S χ ⊆ (V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∀ χ ∈ F, ∀ i ∈ S χ, 1/2 ≤ ((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re ≤ 7/8) →
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        C*((K+1 : ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := fixedStripWindowBand B
  obtain ⟨C₂,hC₂,X₂,h₂⟩ := fixedStripWindowLow B
  let C := max C₁ C₂
  refine ⟨C, hC₁.trans_le (le_max_left ..), max (max X₁ X₂) 2,
    by linarith [le_max_right (max X₁ X₂) (2:ℝ)], ?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF S hS hstrip
  have hX1 := (le_max_left X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hX2 := (le_max_right X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hXp : 0 < X := by linarith [(le_max_right (max X₁ X₂) (2:ℝ)).trans hX]
  have hXge : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => ((V1 χ).zeros i).im) k
  have hpart (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (y : ℝ) :
      zeroWindow χ (S χ) h y =
        ∑ k ∈ range (K+1), zeroWindow χ (P k χ) h y := by
    unfold zeroWindow
    apply V9u
    intro i hi
    exact (ComplexZeroEnumeration.V2r _ _ _).mp (hS χ hχ hi)
  have hpow (k : ℕ) (hk : k ∈ range (K+1)) :
      (2 : ℝ)^(k+1) ≤ 2^(K+1) :=
    pow_le_pow_right₀ (by norm_num) (by have := mem_range.mp hk; omega)
  have hT (k : ℕ) : (2 : ℝ) ≤ 2^(k+1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ k+1 by omega))
  have hlogk (k : ℕ) (hk : k ∈ range (K+1)) :
      Real.log ((Q : ℝ)*2^(k+1)) ≤ 2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (hpow k hk) (Nat.cast_nonneg _)
  have hblock (k : ℕ) (hk : k ∈ range (K+1)) :
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
    by_cases hk0 : k = 0
    · subst k
      have h := h₂ Q hQ X h hX2 hh hhX hscale
        (by simpa using hlogk 0 hk) F hF (P 0)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,_⟩ := mem_filter.mp hi
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr
            (by simpa using hiT),hstrip χ hχ i hiS⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_right ..)
    · have h := h₁ Q hQ X h ((2:ℝ)^(k+1)) hX1 (hT k) hh hhX hscale
        (hlogk k hk) F hF (P k)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,hiL⟩ := mem_filter.mp hi
          have hL' := hiL.resolve_left hk0
          have he : (2:ℝ)^(k+1)/2 = 2^k := by rw [pow_succ]; ring
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr hiT,
            (hstrip χ hχ i hiS).1,(hstrip χ hχ i hiS).2,by rw [he]; exact hL'.le⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_left ..)
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      (∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
    simp_rw [hpart χ hχ]
    simpa only [card_range] using
      (V1dr (range (K+1)) (fun k y => zeroWindow χ (P k χ) h y) X hXp.le
        (fun k _ => ContinuousOn.intervalIntegrable_of_Icc (by linarith)
          ((V6e (P k χ) (V1 χ).zeros X h hXp hh.le hhX).norm.pow 2)))
  calc
    _ ≤ ∑ χ ∈ F, ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) :=
      sum_le_sum hterm
    _ = ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1), ∑ χ ∈ F,
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
      rw [← mul_sum, sum_comm]
    _ ≤ ((K+1 : ℕ):ℝ)*(∑ _k ∈ range (K+1), C*h^2*X/(Real.log X)^B) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hblock) (by positivity)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- Sum all the dyadic bands in the strip 1/2 ≤ Re ρ ≤ 1 - V2j (B+4) X.
The loss is at most (K+1)^2, for U=2^(K+1). -/
theorem goodZerosAllHeights (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ),
      1 ≤ Q → X₀ ≤ X → 0 < h → h ≤ X →
      (Q : ℝ)^2/(h/X) ≤ X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1)) ≤ 2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ ∈ F, S χ ⊆ (V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∀ χ ∈ F, ∀ i ∈ S χ, 1/2 ≤ ((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re ≤ 1 - V1l.V2j (B+4) X) →
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        C*((K+1 : ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := V93.Vz7 B
  obtain ⟨C₂,hC₂,X₂,h₂⟩ := V93.V1ep B
  let C := max C₁ C₂
  refine ⟨C, hC₁.trans_le (le_max_left ..), max (max X₁ X₂) 2,
    by linarith [le_max_right (max X₁ X₂) (2:ℝ)], ?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF S hS hstrip
  have hX1 := (le_max_left X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hX2 := (le_max_right X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hXp : 0 < X := by linarith [(le_max_right (max X₁ X₂) (2:ℝ)).trans hX]
  have hXge : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => ((V1 χ).zeros i).im) k
  have hpart (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (y : ℝ) :
      zeroWindow χ (S χ) h y =
        ∑ k ∈ range (K+1), zeroWindow χ (P k χ) h y := by
    unfold zeroWindow
    apply V9u
    intro i hi
    exact (ComplexZeroEnumeration.V2r _ _ _).mp (hS χ hχ hi)
  have hpow (k : ℕ) (hk : k ∈ range (K+1)) :
      (2 : ℝ)^(k+1) ≤ 2^(K+1) :=
    pow_le_pow_right₀ (by norm_num) (by have := mem_range.mp hk; omega)
  have hT (k : ℕ) : (2 : ℝ) ≤ 2^(k+1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ k+1 by omega))
  have hlogk (k : ℕ) (hk : k ∈ range (K+1)) :
      Real.log ((Q : ℝ)*2^(k+1)) ≤ 2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (hpow k hk) (Nat.cast_nonneg _)
  have hblock (k : ℕ) (hk : k ∈ range (K+1)) :
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
    by_cases hk0 : k = 0
    · subst k
      have h := h₂ Q hQ X h hX2 hh hhX hscale
        (by simpa using hlogk 0 hk) F hF (P 0)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,_⟩ := mem_filter.mp hi
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr
            (by simpa using hiT),hstrip χ hχ i hiS⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_right ..)
    · have h := h₁ Q hQ X h ((2:ℝ)^(k+1)) hX1 (hT k) hh hhX hscale
        (hlogk k hk) F hF (P k)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,hiL⟩ := mem_filter.mp hi
          have hL' := hiL.resolve_left hk0
          have he : (2:ℝ)^(k+1)/2 = 2^k := by rw [pow_succ]; ring
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr hiT,
            (hstrip χ hχ i hiS).1,(hstrip χ hχ i hiS).2,by rw [he]; exact hL'.le⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_left ..)
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      (∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
    simp_rw [hpart χ hχ]
    simpa only [card_range] using
      (V1dr (range (K+1)) (fun k y => zeroWindow χ (P k χ) h y) X hXp.le
        (fun k _ => ContinuousOn.intervalIntegrable_of_Icc (by linarith)
          ((V6e (P k χ) (V1 χ).zeros X h hXp hh.le hhX).norm.pow 2)))
  calc
    _ ≤ ∑ χ ∈ F, ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) :=
      sum_le_sum hterm
    _ = ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1), ∑ χ ∈ F,
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
      rw [← mul_sum, sum_comm]
    _ ≤ ((K+1 : ℕ):ℝ)*(∑ _k ∈ range (K+1), C*h^2*X/(Real.log X)^B) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hblock) (by positivity)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- Moving-average smoothing does not increase energy beyond the
slightly enlarged physical interval. -/
theorem smoothedWindowEnergy
    (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {X h δ : ℝ}
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h ≤ X/2)
    (hδ : 0 < δ) (hδX : δ ≤ X/2) :
    (∑ χ ∈ F, ∫ y in X..2*X, ‖V3q (zeroWindow χ (S χ) h) δ y‖^2) ≤
      (∑ χ ∈ F, ∫ y in X/2..X, ‖zeroWindow χ (S χ) h y‖^2) +
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) := by
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro χ _
  let f := zeroWindow χ (S χ) h
  have hcont : ContinuousOn f (Set.Icc (X/2) (2*X)) := by
    unfold f zeroWindow
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hpos : y+h ≠ 0 := by linarith [hy.1]
      have hc : ContinuousAt (fun t : ℝ => t+h) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+h:ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+h) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+h) ((V1 χ).zeros i) (Or.inr hpos)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y ≠ 0))).continuousWithinAt
  have hsub : Set.Icc (X-δ) (2*X) ⊆ Set.Icc (X/2) (2*X) :=
    Set.Icc_subset_Icc (by linarith) le_rfl
  apply (V1qh f X δ hX.le hδ (hcont.mono hsub)).trans
  have hint : IntervalIntegrable (fun y => ‖f y‖^2) volume (X/2) (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hcont.norm.pow 2)
  calc
    _ ≤ ∫ u in X/2..2*X, ‖f u‖^2 :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith)
        le_rfl (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hint
    _ = _ := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hint.mono_set (by rw [Set.uIcc_of_le (by linarith : X/2≤X),
          Set.uIcc_of_le (by linarith : X/2≤2*X)]; exact Set.Icc_subset_Icc le_rfl (by linarith)))
        (hint.mono_set (by rw [Set.uIcc_of_le (by linarith : X≤2*X),
          Set.uIcc_of_le (by linarith : X/2≤2*X)]; exact Set.Icc_subset_Icc (by linarith) le_rfl))]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPolynomialWindow.lean; sha256 7f4a3a9e90a224457177cafec7417d3f44893c102cdb2a156ec99283481e5fff -/
section
/-!
Adaptation of Vbt.V1mq, V86.Vja, V86.V10t from the accepted
DyadicCellShortPrimeFloor proof (LogTruSoul, PR #3746).
Only the modulus range is changed: Q ≤ X implies log q ≤ log X.
All explicit-formula ingredients are reused, not assumed.
-/

noncomputable section
open Complex Finset MeasureTheory
open scoped Interval BigOperators Classical
open OAI.Ostmann V82 V6i V1e Vx Vex Vbt V7e V86
namespace InnerFloorResearch.PolynomialWindow
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem sqrtLogPolynomial (X q Q u : ℝ)
    (hX : 4≤X) (hq : 1≤q) (hqQ : q≤Q) (hQX : Q≤X)
    (hu : 1≤u) (huX : u≤3*X) :
    Real.sqrt u*(1+Real.log q)≤52*Real.sqrt X*Real.log X := by
  have hXp : 0<X := by linarith
  have hqp : 0<q := by linarith
  have hLp : 0<Real.log X := Real.log_pos (by linarith)
  have hL : 1≤Real.log X := by
    apply (Real.le_log_iff_exp_le hXp).2
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hqlog : Real.log q≤Real.log X := Real.log_le_log hqp (hqQ.trans hQX)
  have hfactor : 1+Real.log q≤26*Real.log X := by linarith
  have hfactor0 : 0≤1+Real.log q := by linarith [Real.log_nonneg hq]
  have hsqrt : Real.sqrt u≤2*Real.sqrt X := by
    calc
      _ ≤ Real.sqrt (4*X) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hm := mul_le_mul hsqrt hfactor hfactor0 (by positivity)
  exact hm.trans_eq (by ring)

theorem smoothedRemainderPolynomial (f : ℝ → ℂ) (E q Q X y h δ : ℝ)
    (hE : 0≤E) (hq : 1≤q) (hqQ : q≤Q) (hQX : Q≤X)
    (hX : 4≤X) (hy : y∈Set.Icc X (2*X)) (hh : 0≤h) (hhX : h≤X)
    (hδ : 0<δ) (hδX : δ≤X/2)
    (hf : ∀ u:ℝ,1≤u → ‖f u‖≤E*Real.sqrt u*(1+Real.log q)) :
    ‖V1c f y h δ‖≤208*E*(Real.sqrt X*Real.log X/δ) := by
  have hb (u : ℝ) (hu : X/2≤u) (huX : u≤3*X) :
      ‖f u‖≤52*E*Real.sqrt X*Real.log X := by
    have hu1 : 1≤u := by linarith
    calc
      _ ≤ E*Real.sqrt u*(1+Real.log q) := hf u hu1
      _ = E*(Real.sqrt u*(1+Real.log q)) := by ring
      _ ≤ E*(52*Real.sqrt X*Real.log X) := mul_le_mul_of_nonneg_left
        (sqrtLogPolynomial X q Q u hX hq hqQ hQX hu1 huX) hE
      _ = _ := by ring
  have he := Vun f y h δ (52*E*Real.sqrt X*Real.log X) hδ
    (hb (y+h) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y+h-δ) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb y (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y-δ) (by linarith [hy.1]) (by linarith [hy.2]))
  exact he.trans_eq (by ring)

theorem nonprincipalWindowFormulaPolynomial :
    ∃ D:ℝ,0<D ∧ ∀ Q:ℕ,1≤Q → ∀ (X y δ U:ℝ) (h:ℕ),
      4≤X → y∈Set.Icc X (2*X) → (h:ℝ)≤X → 1≤δ → δ≤X/2 → 2≤U →
      (Q:ℝ)≤X →
      ∀ χ:PrimitiveComplexCharacter,χ.modulus≤Q →
      ‖V4q χ h y+
        V3q (fun u=>∑ i∈(V1 χ).V14 U,
          Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
        D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
          (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
  obtain ⟨E,hE,hbound⟩ := Vt5
  have hT := Vj5
  refine ⟨20+208*E+V38,by positivity,?_⟩
  intro Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ hχ
  have hX2 : 2≤X := by linarith
  have hδp : 0<δ := by linarith
  have hyδ : δ<y := by linarith [hy.1]
  have hh : (0:ℝ)≤h := Nat.cast_nonneg h
  have hq : 1≤(χ.modulus:ℝ) := by exact_mod_cast χ.positive
  have hqQ : (χ.modulus:ℝ)≤Q := by exact_mod_cast hχ
  have hQr : 1≤(Q:ℝ) := by exact_mod_cast hQ
  have hlogX : 0≤Real.log X := Real.log_nonneg (by linarith)
  have hlogU : 0≤Real.log ((Q:ℝ)*U) := Real.log_nonneg (by nlinarith)
  obtain ⟨c,hc⟩ := hbound χ
  have huns := V1co χ h X y δ hX2 hy hhX hδ hδX
  have hrem := smoothedRemainderPolynomial (V7p χ c)
    E χ.modulus Q X y h δ hE.le hq hqQ hQX hX hy hh hhX hδp hδX hc
  have hori := V1wr χ X y h δ hX2 hy hh hhX hδ hδX
  have htail := V1t6 Q hQ χ hχ X y h δ U hX2 hy hh hhX hδp hδX hU
  have hid := V172 χ c y h δ U hδp hyδ hh
  have hn := V1gu (V4q χ h y) _ _ _ _ _ hid
  have hs : ‖V4q χ h y+
      V3q (fun u=>∑ i∈(V1 χ).V14 U,
        Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
      18*(δ*Real.log X)+(208*E)*(Real.sqrt X*Real.log X/δ)+
        V38*((Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
    linarith
  exact hs.trans (Vwl E (δ*Real.log X) (Real.sqrt X*Real.log X/δ)
    ((Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) hE (by positivity) (by positivity) (by positivity))

end InnerFloorResearch.PolynomialWindow
end

end

/-! BEGIN InnerFloorWindowFormulaEnergy.lean; sha256 87cda253583e6579a54e14ded217a941103080803f5596c58315a528e8ec150e -/
section
/-!
Local energy transfer from the polynomial-modulus explicit formula.
The residual is kept explicit; no zero-free hypothesis is used.
This connects the analytic formula to an actual arithmetic-window L² bound.
-/

open Finset MeasureTheory
open scoped Interval Classical
open OAI.Ostmann V1e V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem windowFormulaEnergy (g f : ℝ → ℂ) {X δ E : ℝ}
    (hX : 0 ≤ X) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hf : ContinuousOn f (Set.Icc (X-δ) (2*X)))
    (hres : ∀ y ∈ Set.Icc X (2*X), ‖g y + V3q f δ y‖ ≤ E) :
    (∫ y in X..2*X, ‖g y‖^2) ≤
      2*X*E^2 + 2*(∫ y in X-δ..2*X, ‖f y‖^2) := by
  have hXX : X ≤ 2*X := by linarith
  obtain ⟨hQ,hFubini⟩ := V16e (fun u => ‖f u‖^2) X δ hX hδ.le
    (hf.norm.pow 2) (fun _ _ => sq_nonneg _)
  have hp : ∀ y ∈ Set.Icc X (2*X),
      ‖g y‖^2 ≤ 2*E^2 + (2/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
    intro y hy
    have hc : ContinuousOn f (Set.Icc (y-δ) y) := hf.mono (by
      intro u hu
      exact ⟨by linarith [hy.1,hu.1],by linarith [hy.2,hu.2]⟩)
    have hs := Vl2.V1gz f (y-δ) y (by linarith) hc
    have hn : ‖V3q f δ y‖^2 ≤ (1/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
      have he : ‖V3q f δ y‖^2 =
          (δ⁻¹)^2*‖∫ u in y-δ..y,f u‖^2 := by
        rw [V3q,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hδ.le,mul_pow]
      rw [he]
      apply (mul_le_mul_of_nonneg_left hs (sq_nonneg (δ⁻¹))).trans_eq
      field_simp
      <;> ring
    have hnorm : ‖g y‖ ≤ E + ‖V3q f δ y‖ := by
      have h := norm_sub_le (g y + V3q f δ y) (V3q f δ y)
      rw [add_sub_cancel_right] at h
      linarith [hres y hy]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hs' : (E + ‖V3q f δ y‖)^2 ≤ 2*E^2+2*‖V3q f δ y‖^2 := by
      nlinarith [sq_nonneg (E-‖V3q f δ y‖)]
    refine hsq.trans (hs'.trans ?_)
    calc
      _ ≤ 2*E^2+2*((1/δ)*(∫ u in y-δ..y, ‖f u‖^2)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤2)) _
      _ = _ := by ring
  have hi : (∫ y in X..2*X, ‖g y‖^2) ≤
      ∫ y in X..2*X, 2*E^2 + (2/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
    rw [intervalIntegral.integral_of_le hXX,intervalIntegral.integral_of_le hXX]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (intervalIntegrable_const.add (hQ.const_mul (2/δ))).1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact hp y ⟨hy.1.le,hy.2⟩
  rw [intervalIntegral.integral_add intervalIntegrable_const (hQ.const_mul (2/δ)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul] at hi
  calc
    _ ≤ (2*X-X)*(2*E^2)+(2/δ)*(∫ y in X..2*X,∫ u in y-δ..y,‖f u‖^2) := hi
    _ ≤ (2*X-X)*(2*E^2)+(2/δ)*(δ*(∫ u in X-δ..2*X,‖f u‖^2)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hFubini (by positivity : 0≤(2:ℝ)/δ)) _
    _ = _ := by field_simp; ring

/-- The actual nonprincipal von Mangoldt short-window family is bounded by
the explicit formula residual plus the full zero-window energy. -/
theorem primitiveWindowEnergyFromZeros :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (X δ U : ℝ) (h : ℕ), 4 ≤ X → (h:ℝ) ≤ X →
      1 ≤ δ → δ ≤ X/2 → 2 ≤ U → (Q:ℝ) ≤ X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))
      (∑ χ∈F, ∫ y in X..2*X, ‖V4q χ h y‖^2) ≤
        2*X*(Q:ℝ)^2*E^2 +
          2*(∑ χ∈F, ∫ y in X-δ..2*X,
            ‖∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)‖^2) := by
  obtain ⟨D,hD,hformula⟩ := PolynomialWindow.nonprincipalWindowFormulaPolynomial
  refine ⟨D,hD,?_⟩
  intro Q hQ X δ U h hX hhX hδ hδX hU hQX F hF
  dsimp only
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))
  let f (χ : PrimitiveComplexCharacter) (y : ℝ) :=
    ∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)
  have hE : 0 ≤ E := by
    have hL : 0≤Real.log X := Real.log_nonneg (by linarith)
    have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
    have hL2 : 0≤Real.log ((Q:ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQr (by linarith))
    dsimp [E]
    positivity
  have hcont (χ : PrimitiveComplexCharacter) :
      ContinuousOn (f χ) (Set.Icc (X-δ) (2*X)) := by
    unfold f
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+(h:ℝ) ≠ 0 := by linarith [hy.1, Nat.cast_nonneg (α := ℝ) h]
      have hc : ContinuousAt (fun t:ℝ => t+(h:ℝ)) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+(h:ℝ):ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+(h:ℝ)) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+(h:ℝ)) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ∈F) :
      (∫ y in X..2*X, ‖V4q χ h y‖^2) ≤
        2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2) :=
    windowFormulaEnergy (V4q χ h) (f χ) (by linarith) (by linarith) hE
      (hcont χ) (fun y hy =>
        hformula Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ (hF χ hχ))
  have hcard : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
  change _ ≤ 2*X*(Q:ℝ)^2*E^2 + 2*(∑ χ∈F, ∫ y in X-δ..2*X,‖f χ y‖^2)
  calc
    _ ≤ ∑ χ∈F, (2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2)) :=
      sum_le_sum hterm
    _ = (F.card:ℝ)*(2*X*E^2)+2*(∑ χ∈F,∫ y in X-δ..2*X,‖f χ y‖^2) := by
      rw [sum_add_distrib,← mul_sum]
      simp only [sum_const,nsmul_eq_mul]
      rw [← mul_sum]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hcard (by positivity : 0≤2*X*E^2)
      linarith

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFullSpectrum.lean; sha256 7500843247d0a2ec7e25d286557ef631dc7673d29fffe5e2d350ae909790ad45 -/
section
/-!
Full-spectrum energy with an explicitly retained near-one term.
No fixed zero-free strip is assumed or asserted.
-/
open Finset MeasureTheory Filter
open scoped Classical Interval Topology
open OAI.Ostmann V1e V6b V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def leftIndices (χ : PrimitiveComplexCharacter) (U : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => ((V1 χ).zeros i).re ≤ (2:ℝ)⁻¹

def rightGoodIndices (χ : PrimitiveComplexCharacter) (U c : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => (2:ℝ)⁻¹ < ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ c

def rightBadIndices (χ : PrimitiveComplexCharacter) (U c : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => (2:ℝ)⁻¹ < ((V1 χ).zeros i).re ∧ c < ((V1 χ).zeros i).re

theorem zeroWindow_partition (χ : PrimitiveComplexCharacter) (U c h y : ℝ) :
    zeroWindow χ ((V1 χ).V14 U) h y =
      zeroWindow χ (leftIndices χ U) h y +
      zeroWindow χ (rightGoodIndices χ U c) h y +
      zeroWindow χ (rightBadIndices χ U c) h y := by
  classical
  unfold zeroWindow leftIndices rightGoodIndices rightBadIndices
  simp only [sum_filter]
  rw [← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hl : ((V1 χ).zeros i).re ≤ (2:ℝ)⁻¹
  · simp [hl,not_lt_of_ge hl]
  · have hr := lt_of_not_ge hl
    by_cases hg : ((V1 χ).zeros i).re ≤ c
    · simp [hl,hr,hg,not_lt_of_ge hg]
    · simp [hl,hr,hg,lt_of_not_ge hg]

def zeroFamilyEnergy (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) (X h : ℝ) : ℝ :=
  ∑ χ∈F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2

theorem zeroFamilyEnergy_nonneg (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {X h : ℝ} (hX : 0≤X) :
    0≤zeroFamilyEnergy F S X h :=
  sum_nonneg fun _ _ => intervalIntegral.integral_nonneg_of_forall (by linarith)
    fun _ => sq_nonneg _

/-- Only the last, near-one spectral term is uncontrolled. The
factor 3 follows from finite Cauchy--Schwarz rather than cancellation. -/
theorem fullSpectrumSplit (F : Finset PrimitiveComplexCharacter)
    (U c X h : ℝ) (hX : 0<X) (hh : 0≤h) (hhX : h≤X) :
    zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h ≤
      3*(zeroFamilyEnergy F (fun χ => leftIndices χ U) X h +
        zeroFamilyEnergy F (fun χ => rightGoodIndices χ U c) X h +
        zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h) := by
  let f (χ : PrimitiveComplexCharacter) (i : ℕ) (y : ℝ) :=
    if i=0 then zeroWindow χ (leftIndices χ U) h y
    else if i=1 then zeroWindow χ (rightGoodIndices χ U c) h y
    else zeroWindow χ (rightBadIndices χ U c) h y
  have hp (χ : PrimitiveComplexCharacter) (y : ℝ) :
      (∑ i∈range 3,f χ i y) = zeroWindow χ ((V1 χ).V14 U) h y := by
    rw [zeroWindow_partition χ U c h y]
    norm_num [f,Finset.sum_range_succ]
  have hi (χ : PrimitiveComplexCharacter) (i : ℕ) :
      IntervalIntegrable (fun y => ‖f χ i y‖^2) volume X (2*X) := by
    unfold f
    split_ifs <;> apply ContinuousOn.intervalIntegrable_of_Icc (by linarith) <;>
      exact (V6e _ (V1 χ).zeros X h hX hh hhX).norm.pow 2
  unfold zeroFamilyEnergy
  rw [← sum_add_distrib,← sum_add_distrib,mul_sum]
  apply sum_le_sum
  intro χ _
  have hs := V1dr (range 3) (f χ) X hX.le (fun i _ => hi χ i)
  simp_rw [hp] at hs
  simpa [f,Finset.sum_range_succ] using hs

/-- Existing zero density bounds close the entire good part, leaving
only the explicitly filtered near-one packet. -/
theorem fullSpectrumEnergyWithResidual (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ), 1≤Q → X₀≤X → 0<h → h≤X →
      (Q:ℝ)^2/(h/X)≤X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F,χ.modulus≤Q) →
      let U := (2:ℝ)^(K+1)
      let c := 1-V1l.V2j (B+4) X
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h ≤
        C*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
        3*zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := V9h.V1jv B
  obtain ⟨C₂,hC₂,X₂,_,h₂⟩ := goodZerosAllHeights B
  refine ⟨3*(C₁+C₂),by positivity,max 2 (max X₁ X₂),le_max_left ..,?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF
  dsimp only
  let U := (2:ℝ)^(K+1)
  let c := 1-V1l.V2j (B+4) X
  have hX1 : X₁≤X := (le_max_left X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hX2 : X₂≤X := (le_max_right X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hXge : 2≤X := (le_max_left _ _).trans hX
  have hXp : 0<X := by linarith
  have hL : 0<Real.log X := Real.log_pos (by linarith)
  have hleft := h₁ Q hQ K X h hX1 hh hhX hscale hlog F hF
    (fun χ => leftIndices χ U)
    (fun χ _ => filter_subset _ _) (fun χ _ i hi => by simpa only [one_div] using (mem_filter.mp hi).2)
  have hright := h₂ Q K X h hQ hX2 hh hhX hscale hlog F hF
    (fun χ => rightGoodIndices χ U c)
    (fun χ _ => filter_subset _ _)
    (fun χ _ i hi => ⟨by simpa only [one_div] using (mem_filter.mp hi).2.1.le,(mem_filter.mp hi).2.2⟩)
  have hleft' : zeroFamilyEnergy F (fun χ => leftIndices χ U) X h ≤
      C₁*h^2*X/(Real.log X)^B := hleft
  have hright' : zeroFamilyEnergy F (fun χ => rightGoodIndices χ U c) X h ≤
      C₂*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := hright
  have hk : (1:ℝ)≤((K+1:ℕ):ℝ) := by exact_mod_cast (show 1≤K+1 by omega)
  have hleft'' : zeroFamilyEnergy F (fun χ => leftIndices χ U) X h ≤
      C₁*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
    apply hleft'.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hXp.le
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg h)
    calc
      C₁ = C₁*1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hk,sq_nonneg (((K+1:ℕ):ℝ)-1)]) hC₁.le
  calc
    _ ≤ _ := fullSpectrumSplit F U c X h hXp hh.le hhX
    _ ≤ 3*(C₁*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
      C₂*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
      zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h) :=
      mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add hleft'' hright') _)
        (by norm_num)
    _ = _ := by ring


/-- Any fixed positive strip gap, not only 7/8, eliminates the bad packet
eventually. The input is a genuine hypothesis and is not assumed by the
unconditional residual theorem. -/
theorem eventually_badIndices_empty_of_uniform_gap (A : ℕ)
    (σ : ℝ) (hσ : σ < 1)
    (hgap : ∀ (χ : PrimitiveComplexCharacter) (i : ℕ),
      ((V1 χ).zeros i).re ≤ σ) :
    ∀ᶠ X : ℝ in atTop, ∀ (χ : PrimitiveComplexCharacter) (U : ℝ),
      rightBadIndices χ U (1-V1l.V2j A X)=∅ := by
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hc : Tendsto (V1l.V2j A) atTop (𝓝 0) := by
    have hm := ht.const_mul (3 * (A+14 : ℕ) : ℝ)
    simp only [mul_zero] at hm
    convert hm using 1
    ext X
    simp only [V1l.V2j, mul_div_assoc]
  filter_upwards [hc.eventually (gt_mem_nhds (sub_pos.mpr hσ))] with X hδ
  intro χ U
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hbad := (Finset.mem_filter.mp hi).2.2
  linarith [hgap χ i]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPrimeSpectralTransfer.lean; sha256 4237cac1e58a0b9e150fdb7b9180da7e4d37008f19ddc3376b178c8b3098210b -/
section
/-!
Use the smoothed explicit formula directly for the log-prime window.
The von Mangoldt-to-prime correction is absorbed pointwise in E; there
is no extra integral triangle or integrability obligation for the
arithmetic step functions.
-/
open Finset MeasureTheory Filter
open scoped Classical Interval Topology
open OAI.Ostmann V1e V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem primitivePrimeEnergyFromZeros :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (X δ U : ℝ) (h : ℕ), 4 ≤ X → (h:ℝ) ≤ X →
      1 ≤ δ → δ ≤ X/2 → 2 ≤ U → (Q:ℝ) ≤ X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) + 2*Real.sqrt (3*X)*Real.log (3*X)
      (∑ χ∈F, ∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*(Q:ℝ)^2*E^2 +
          2*(∑ χ∈F, ∫ y in X-δ..2*X,
            ‖∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)‖^2) := by
  obtain ⟨D,hD,hformula⟩ := PolynomialWindow.nonprincipalWindowFormulaPolynomial
  refine ⟨D,hD,?_⟩
  intro Q hQ X δ U h hX hhX hδ hδX hU hQX F hF
  dsimp only
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) + 2*Real.sqrt (3*X)*Real.log (3*X)
  let f (χ : PrimitiveComplexCharacter) (y : ℝ) :=
    ∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)
  have hE : 0 ≤ E := by
    have hL : 0≤Real.log X := Real.log_nonneg (by linarith)
    have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
    have hL2 : 0≤Real.log ((Q:ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQr (by linarith))
    have hL3 : 0≤Real.log (3*X) := Real.log_nonneg (by linarith)
    dsimp [E]
    positivity
  have hcont (χ : PrimitiveComplexCharacter) :
      ContinuousOn (f χ) (Set.Icc (X-δ) (2*X)) := by
    unfold f
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+(h:ℝ) ≠ 0 := by linarith [hy.1, Nat.cast_nonneg (α := ℝ) h]
      have hc : ContinuousAt (fun t:ℝ => t+(h:ℝ)) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+(h:ℝ):ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+(h:ℝ)) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+(h:ℝ)) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ∈F) :
      (∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2) :=
    windowFormulaEnergy (fun y => InnerFloorAP.centeredPrimeSum χ.character y h) (f χ) (by linarith) (by linarith) hE
      (hcont χ) (fun y hy =>
        by
          have ha := hformula Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ (hF χ hχ)
          have hb := (centeredPrimeWindowError χ h
            (by linarith [hy.1]) (show y+(h:ℝ)≤3*X by linarith [hy.2])).trans
            (Chebyshev.psi_sub_theta_le (show 1≤3*X by linarith))
          have hdiff : ‖InnerFloorAP.centeredPrimeSum χ.character y h - V4q χ h y‖ ≤
              2*Real.sqrt (3*X)*Real.log (3*X) := by
            rw [norm_sub_rev]
            exact hb
          have hsplit : InnerFloorAP.centeredPrimeSum χ.character y h + V3q (f χ) δ y =
              (V4q χ h y + V3q (f χ) δ y) +
                (InnerFloorAP.centeredPrimeSum χ.character y h - V4q χ h y) := by abel
          rw [hsplit]
          exact (norm_add_le _ _).trans (add_le_add ha hdiff))
  have hcard : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
  change _ ≤ 2*X*(Q:ℝ)^2*E^2 + 2*(∑ χ∈F, ∫ y in X-δ..2*X,‖f χ y‖^2)
  calc
    _ ≤ ∑ χ∈F, (2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2)) :=
      sum_le_sum hterm
    _ = (F.card:ℝ)*(2*X*E^2)+2*(∑ χ∈F,∫ y in X-δ..2*X,‖f χ y‖^2) := by
      rw [sum_add_distrib,← mul_sum]
      simp only [sum_const,nsmul_eq_mul]
      rw [← mul_sum]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hcard (by positivity : 0≤2*X*E^2)
      linarith


/-- The enlarged smoothing interval is covered by two adjacent dyadic
intervals, so no unproved estimate on a non-dyadic segment is needed. -/
theorem enlargedZeroWindowEnergy_le
    (F : Finset PrimitiveComplexCharacter) (U X h δ : ℝ)
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h≤X/2)
    (hδ : 0≤δ) (hδX : δ≤X/2) :
    (∑ χ∈F, ∫ y in X-δ..2*X, ‖zeroWindow χ ((V1 χ).V14 U) h y‖^2) ≤
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) (X/2) h +
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h := by
  unfold zeroFamilyEnergy
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro χ _
  let f (y:ℝ) := ‖zeroWindow χ ((V1 χ).V14 U) h y‖^2
  have hcont : ContinuousOn f (Set.Icc (X/2) (2*X)) := by
    unfold f
    apply ContinuousOn.pow
    unfold zeroWindow
    apply ContinuousOn.norm
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+h≠0 := by linarith [hy.1]
      have hc : ContinuousAt (fun t:ℝ => t+h) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t:ℝ => ((t+h:ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+h) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+h) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hi : IntervalIntegrable f volume (X/2) (2*X) :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hsplit : (∫ y in X/2..2*X,f y) =
      (∫ y in X/2..X,f y)+(∫ y in X..2*X,f y) := by
    have h₁ : IntervalIntegrable f volume (X/2) X :=
      (hcont.mono (Set.Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (by linarith)
    have h₂ : IntervalIntegrable f volume X (2*X) :=
      (hcont.mono (Set.Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by linarith)
    exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm
  change (∫ y in X-δ..2*X,f y) ≤
    (∫ y in X/2..2*(X/2),f y)+(∫ y in X..2*X,f y)
  rw [show 2*(X/2)=X by ring,← hsplit]
  rw [intervalIntegral.integral_of_le (by linarith : X-δ≤2*X),
    intervalIntegral.integral_of_le (by linarith : X/2≤2*X)]
  have hI : IntegrableOn f (Set.Ioc (X/2) (2*X)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X/2≤2*X)).1 hi
  exact setIntegral_mono_set hI (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ hy => ⟨by linarith [hy.1],hy.2⟩)


/-- Actual prime energy, with an explicit and isolated exceptional
spectral residual. Both dyadic spectral inputs are theorems, not
hypotheses. The only potentially large terms are the two bad packets. -/
theorem primitivePrimeEnergyWithResidual (B : ℕ) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∃ X₀ : ℝ, 4 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X δ : ℝ) (h : ℕ), 1 ≤ Q → X₀ ≤ X → 0 < h →
      (h:ℝ) ≤ X/2 → 1 ≤ δ → δ ≤ X/2 → (Q:ℝ) ≤ X →
      (Q:ℝ)^2/((h:ℝ)/(X/2)) ≤ (X/2)^(5/12:ℝ) →
      (Q:ℝ)^2/((h:ℝ)/X) ≤ X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log (X/2) →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F,χ.modulus≤Q) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*X)*Real.log (3*X)
      let R (Y:ℝ) := zeroFamilyEnergy F
        (fun χ => rightBadIndices χ U (1-V1l.V2j (B+4) Y)) Y h
      (∑ χ∈F, ∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*(Q:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X/2)/(Real.log (X/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*X/(Real.log X)^B+
        6*(R (X/2)+R X) := by
  obtain ⟨D,hD,hd⟩ := primitivePrimeEnergyFromZeros
  obtain ⟨C,hC,Y₀,hY₀,hc⟩ := fullSpectrumEnergyWithResidual B
  refine ⟨D,C,hD,hC,max 4 (2*Y₀),le_max_left ..,?_⟩
  intro Q K X δ h hQ hX hh hhX hδ hδX hQX hscale₁ hscale₂ hlog F hF
  dsimp only
  let U := (2:ℝ)^(K+1)
  have hX4 : 4≤X := (le_max_left _ _).trans hX
  have hXp : 0 < X := by linarith
  have hY : Y₀≤X/2 := by linarith [(le_max_right (4:ℝ) (2*Y₀)).trans hX]
  have hY' : Y₀≤X := by linarith
  have hU : 2≤U := by
    dsimp [U]
    rw [pow_succ]
    have hk : (1:ℝ)≤(2:ℝ)^K := one_le_pow₀ (by norm_num)
    nlinarith only [hk]
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hlog' : Real.log ((Q:ℝ)*U)≤2*Real.log X :=
    hlog.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith : 0 < X/2) (by linarith)) (by norm_num))
  have he := hd Q hQ X δ U h hX4 (by linarith) hδ hδX hU hQX F hF
  dsimp only at he
  have hz := enlargedZeroWindowEnergy_le F U X h δ hXp hh'.le hhX (by linarith) hδX
  have h1 := hc Q K (X/2) h hQ hY hh' hhX hscale₁ hlog F hF
  have h2 := hc Q K X h hQ hY' hh' (by linarith) hscale₂ hlog' F hF
  dsimp only at h1 h2
  change (∑ χ∈F, ∫ y in X-δ..2*X,‖zeroWindow χ ((V1 χ).V14 U) h y‖^2) ≤ _ at hz
  unfold zeroWindow at hz
  dsimp only [U] at he hz
  have hZ := hz.trans (add_le_add h1 h2)
  have hT := he.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hZ (by norm_num : (0:ℝ) ≤ 2)))
  exact hT.trans_eq (by ring)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorUniformStripBridge.lean; sha256 2aece9ebc1c75e3c24a407777d535c7b6fc0655f89aa8a39f8820e8d891f1a73 -/
section
/-!
An explicit adapter for the public Dirichlet L-function nonvanishing
statement. It does not import that theorem and does not assert it.
The proof needs an approved unconditional theorem of this exact type
(or a weaker uniform positive strip gap). No new axioms are introduced.
-/
open Finset Filter MeasureTheory
open scoped Classical Interval Topology
open OAI.Ostmann V1e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def DirichletUniformStrip (σ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    σ < s.re → ¬(χ=1 ∧ s=1) → DirichletCharacter.LFunction χ s ≠ 0

theorem uniformStrip_enumeratedGap {σ : ℝ} (hs : DirichletUniformStrip σ) :
    ∀ (χ : PrimitiveComplexCharacter) (i : ℕ),
      ((V1 χ).zeros i).re ≤ σ := by
  intro χ i
  by_contra! hi
  letI : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact hs χ.modulus χ.character ((V1 χ).zeros i) hi
    (fun h => χ.nontrivial h.1) ((V1 χ).actual_zero i)

theorem fullSpectrumEnergy_of_uniformStrip {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ), 1≤Q → X₀≤X → 0 < h → h≤X →
      (Q:ℝ)^2/(h/X)≤X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F,χ.modulus≤Q) →
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 ((2:ℝ)^(K+1))) X h ≤
        C*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,hX₁,hbound⟩ := fullSpectrumEnergyWithResidual B
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (eventually_badIndices_empty_of_uniform_gap (B+4) σ hσ
      (uniformStrip_enumeratedGap hs))
  refine ⟨C,hC,max X₁ X₂,hX₁.trans (le_max_left ..),?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF
  have hb := hbound Q K X h hQ ((le_max_left X₁ X₂).trans hX)
    hh hhX hscale hlog F hF
  dsimp only at hb
  have hz : zeroFamilyEnergy F
      (fun χ => rightBadIndices χ ((2:ℝ)^(K+1)) (1-V1l.V2j (B+4) X)) X h = 0 := by
    unfold zeroFamilyEnergy
    apply sum_eq_zero
    intro χ _
    dsimp only
    rw [hX₂ X ((le_max_right X₁ X₂).trans hX) χ ((2:ℝ)^(K+1))]
    simp [zeroWindow]
  rw [hz,mul_zero,add_zero] at hb
  exact hb

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorActualFamilyBlock.lean; sha256 dedf330dfe9d8457875cf64046a38be2c0dce32a9cdafa44fe5f21fe64f3381a -/
section
/-!
The actual arithmetic family on an integer dyadic block, including the
principal character. This uses the exact step-integral identity, rather
than assuming measurability of a new family or losing a logarithm.
The nonprincipal exceptional spectral residual is not removed here.
-/
open Finset MeasureTheory Filter OAI.Ostmann
open scoped Classical Interval Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem actualNonprincipalBlock_eq_integral (A X h : ℕ) :
    (∑ y∈Ico X (2*X),∑ χ∈analyticPrimitiveFamily A,
        ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) =
      ∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ), ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro χ hχ
  have H := integer_step_integral X (2*X) (by omega)
    (fun y : ℝ => ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)
    (fun y : ℕ => ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)
    (by
      intro k y hy
      rw [centeredPrimeSum_on_unit χ.character k h hy])
  push_cast at H
  exact H.symm

theorem actualPrimitiveBlockWithNonprincipal :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (A X h : ℕ), X₀≤(X:ℝ) → h≤X →
        (2*(X:ℝ))^(4/5:ℝ)≤(h:ℝ) →
      (∑ y∈Ico X (2*X), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
      (∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ), ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
      C*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨C,hC,X₀,hX₀,hCbound⟩ := principalPrimeWindowLogFour
  refine ⟨C^2,by positivity,X₀,hX₀,?_⟩
  intro A X h hX hhX hhlow
  have hX2 : (2:ℝ)≤X := hX₀.trans hX
  have hXp : (0:ℝ) < X := by linarith
  have hlogX : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  let P (y : ℕ) := ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖^2
  have hp (y : ℕ) (hy : y∈Ico X (2*X)) :
      P y≤(C*(h:ℝ)/(Real.log (X:ℝ))^4)^2 := by
    have hy₁ : (X:ℝ)≤y := by exact_mod_cast (mem_Ico.mp hy).1
    have hy₂ : (y:ℝ)≤2*(X:ℝ) := by exact_mod_cast (mem_Ico.mp hy).2.le
    have hylow : (y:ℝ)^(4/5:ℝ)≤(h:ℝ) :=
      (Real.rpow_le_rpow (by positivity) hy₂ (by norm_num)).trans hhlow
    have hyh : (h:ℝ)≤y := (by exact_mod_cast hhX : (h:ℝ)≤X).trans hy₁
    have he := hCbound y (hX.trans hy₁) h hylow hyh (1:DirichletCharacter ℂ 1)
    have hl : Real.log (X:ℝ)≤Real.log (y:ℝ) := Real.log_le_log hXp hy₁
    have hden : (Real.log (X:ℝ))^4≤(Real.log (y:ℝ))^4 :=
      pow_le_pow_left₀ hlogX.le hl 4
    have hb : ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖ ≤
        C*(h:ℝ)/(Real.log (X:ℝ))^4 :=
      he.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hlogX _) hden)
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hP : (∑ y∈Ico X (2*X),P y) ≤
      C^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
    calc
      _ ≤ ∑ _y∈Ico X (2*X),(C*(h:ℝ)/(Real.log (X:ℝ))^4)^2 := sum_le_sum hp
      _ = _ := by
        rw [sum_const,nsmul_eq_mul,Nat.card_Ico,show 2*X-X=X by omega]
        ring
  calc
    _ ≤ ∑ y∈Ico X (2*X),
        ((∑ χ∈analyticPrimitiveFamily A,
          ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)+P y) :=
      sum_le_sum fun y _ => primitiveEnergy_le_analyticFamily A y h
    _ = (∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ),‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
        ∑ y∈Ico X (2*X),P y := by
      rw [sum_add_distrib,actualNonprincipalBlock_eq_integral]
    _ ≤ _ := add_le_add le_rfl hP

/-- Direct actual arithmetic block bound. No unknown arithmetic family
or all-residue model appears: only the two explicitly defined spectral
residuals remain. -/
theorem actualPrimitiveBlockWithResidual (B : ℕ) :
    ∃ D C P : ℝ, 0 < D ∧ 0 < C ∧ 0 < P ∧ ∃ X₀ : ℝ, 4≤X₀ ∧
      ∀ (A X h K : ℕ) (δ : ℝ), 1≤A → X₀≤(X:ℝ) → 0 < h →
      (2*(X:ℝ))^(4/5:ℝ)≤(h:ℝ) → (h:ℝ)≤(X:ℝ)/2 →
      1≤δ → δ≤(X:ℝ)/2 → A≤X →
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2))≤((X:ℝ)/2)^(5/12:ℝ) →
      (A:ℝ)^2/((h:ℝ)/(X:ℝ))≤(X:ℝ)^(5/12:ℝ) →
      Real.log ((A:ℝ)*(2:ℝ)^(K+1))≤2*Real.log ((X:ℝ)/2) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
      let R (Y:ℝ) := zeroFamilyEnergy (analyticPrimitiveFamily A)
        (fun χ => rightBadIndices χ U (1-V1l.V2j (B+4) Y)) Y h
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        2*(X:ℝ)*(A:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*((X:ℝ)/2)/(Real.log ((X:ℝ)/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^B+
        6*(R ((X:ℝ)/2)+R X)+
        P*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨D,C,hD,hC,X₁,hX₁,hbound⟩ := primitivePrimeEnergyWithResidual B
  obtain ⟨P,hP,X₂,hX₂,hprincipal⟩ := actualPrimitiveBlockWithNonprincipal
  refine ⟨D,C,P,hD,hC,hP,max X₁ X₂,hX₁.trans (le_max_left ..),?_⟩
  intro A X h K δ hA hX hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  dsimp only
  have hX₁' : X₁≤(X:ℝ) := (le_max_left _ _).trans hX
  have hX₂' : X₂≤(X:ℝ) := (le_max_right _ _).trans hX
  have hh' : h≤X := by
    exact_mod_cast hhX.trans (by linarith [Nat.cast_nonneg (α:=ℝ) X] : (X:ℝ)/2≤X)
  have H := hprincipal A X h hX₂' hh' hlow
  have G := hbound A K X δ h hA hX₁' hh hhX hδ hδX
    (by exact_mod_cast hAX) hs₁ hs₂ hlog (analyticPrimitiveFamily A)
      (analyticPrimitiveFamily_modulus A)
  dsimp only at G
  exact H.trans (add_le_add G le_rfl)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorUniformStripArithmetic.lean; sha256 46a990b4e8a7cd3d01559216b61bb11bb71a6bdc4e808bf658ffd213819dfc5a -/
section
/-! The actual primitive arithmetic family estimate with the sole
remaining analytic input, a uniform positive zero-free strip.
This is an implication, not a proof of the strip or frozen floor. -/
open Filter Finset MeasureTheory OAI.Ostmann
open scoped Classical Interval Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem actualPrimitiveBlockOfUniformStrip {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) (B : ℕ) :
    ∃ D C P : ℝ, 0 < D ∧ 0 < C ∧ 0 < P ∧ ∃ X₀ : ℝ, 4 ≤ X₀ ∧
      ∀ (A X h K : ℕ) (δ : ℝ), 1 ≤ A → X₀ ≤ (X:ℝ) → 0 < h →
      (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) → (h:ℝ) ≤ (X:ℝ)/2 →
      1 ≤ δ → δ ≤ (X:ℝ)/2 → A ≤ X →
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2)) ≤ ((X:ℝ)/2)^(5/12:ℝ) →
      (A:ℝ)^2/((h:ℝ)/(X:ℝ)) ≤ (X:ℝ)^(5/12:ℝ) →
      Real.log ((A:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log ((X:ℝ)/2) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        2*(X:ℝ)*(A:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*((X:ℝ)/2)/(Real.log ((X:ℝ)/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^B+
        P*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨D,C,P,hD,hC,hP,X₁,hX₁,hbound⟩ := actualPrimitiveBlockWithResidual B
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (eventually_badIndices_empty_of_uniform_gap (B+4) σ hσ
      (uniformStrip_enumeratedGap hs))
  refine ⟨D,C,P,hD,hC,hP,max X₁ (2*max X₂ 1),hX₁.trans (le_max_left ..),?_⟩
  intro A X h K δ hA hX hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  have hx₁ : X₁ ≤ (X:ℝ) := (le_max_left _ _).trans hX
  have hx₂ : X₂ ≤ (X:ℝ)/2 := by
    have H := (le_max_right X₁ (2*max X₂ 1)).trans hX
    linarith only [H,le_max_left X₂ 1]
  have hx₂' : X₂ ≤ (X:ℝ) := by linarith only [hx₂,Nat.cast_nonneg (α:=ℝ) X]
  have G := hbound A X h K δ hA hx₁ hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  dsimp only at G ⊢
  have hz (Y : ℝ) (hY : X₂ ≤ Y) :
      zeroFamilyEnergy (analyticPrimitiveFamily A)
        (fun χ => rightBadIndices χ ((2:ℝ)^(K+1)) (1-V1l.V2j (B+4) Y)) Y h = 0 := by
    unfold zeroFamilyEnergy
    apply sum_eq_zero
    intro χ _
    dsimp only
    rw [hX₂ Y hY χ ((2:ℝ)^(K+1))]
    simp [zeroWindow]
  rw [hz _ hx₂,hz _ hx₂',add_zero,mul_zero,add_zero] at G
  exact G

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorWindowScale.lean; sha256 67b13ea87fca3619b3991bcfb84e0ca10f1f55d1e31dfa992d4b03ab4a69acdf -/
section
open Filter Finset
open scoped Topology

namespace InnerFloorResearch

noncomputable section

abbrev innerCutoff := GoldbachGRHBudget.narrow
noncomputable abbrev outerCutoff := GoldbachGRHBudget.cutoff

def innerWidth (n : ℕ) : ℝ := (innerCutoff n : ℝ) * (n : ℝ) ^ (1/6 : ℝ)
def middleCutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1/5 : ℝ)⌋₊
def innerWindow (n : ℕ) : ℕ := ⌊(n : ℝ) / (12 * innerWidth n)⌋₊

private theorem narrow_le_log (n : ℕ) (hn : 2 ≤ n) :
    (innerCutoff n : ℝ) ≤ 16 * (Real.log (n : ℝ)) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ (Nat.log 2 (n+2)) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n : ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2
    (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0 ≤ (_ : ℝ))
  have hL : (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    push_cast at hraw hlog
    linarith only [hraw, hlog, hm]
  unfold innerCutoff GoldbachGRHBudget.narrow
  push_cast
  calc
    _ ≤ (4 * Real.log (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
    _ = _ := by ring

/-- The real inner radius fits the frozen wide-arc budget. -/
theorem eventualInnerGeometry : ∀ᶠ n : ℕ in atTop,
    2 ≤ n ∧ 1 ≤ innerCutoff n ∧ innerCutoff n ≤ middleCutoff n ∧
    middleCutoff n ≤ outerCutoff n ∧ innerWidth n ≤ (GoldbachGRHBudget.width n : ℝ) ∧
    2 * (GoldbachGRHBudget.width n : ℝ) * (outerCutoff n : ℝ) < (n : ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/5) (1/16) (by norm_num) (by norm_num)]
    with n hg hlog
  obtain ⟨hn, hQ, hQB, _, _, hbudget⟩ := hg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hQA : innerCutoff n ≤ middleCutoff n := by
    apply Nat.le_floor
    calc
      _ ≤ 16 * (Real.log (n : ℝ))^2 := narrow_le_log n hn
      _ ≤ (n : ℝ)^(1/5 : ℝ) := by linarith
  have hAB : middleCutoff n ≤ outerCutoff n := by
    apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have hB1 : (1 : ℝ) ≤ outerCutoff n := by exact_mod_cast hQ.trans hQB
  have h6 : (n : ℝ)^(1/6 : ℝ) ≤ 2 * (outerCutoff n : ℝ) := by
    have hf := Nat.lt_floor_add_one ((n : ℝ)^(1/3 : ℝ))
    change (n : ℝ)^(1/3 : ℝ) < (outerCutoff n : ℝ) + 1 at hf
    exact (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)).trans
      (show (n : ℝ)^(1/3 : ℝ) ≤ 2 * (outerCutoff n : ℝ) by linarith)
  refine ⟨hn, hQ, hQA, hAB, ?_, ?_⟩
  · unfold innerWidth GoldbachGRHBudget.width
    push_cast
    have hQ₀ : 0 ≤ (innerCutoff n : ℝ) := Nat.cast_nonneg _
    have hB₀ : 0 ≤ (outerCutoff n : ℝ) := Nat.cast_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left h6 hQ₀, mul_nonneg hQ₀ hB₀]
  · exact_mod_cast hbudget

/-- One common window for all inner-arc denominators, with a power margin
in the high-exponent short-progression hypothesis. -/
theorem eventualInnerWindow : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (4/5 : ℝ) ≤ (innerWindow n : ℝ) ∧ innerWindow n ≤ n ∧
    6 * (innerWindow n : ℝ) * innerWidth n ≤ (n : ℝ) := by
  filter_upwards [eventualInnerGeometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/30) (1/384) (by norm_num) (by norm_num)]
    with n hg hlog
  obtain ⟨hn, hQ, _, _, _, _⟩ := hg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hQ' : (1 : ℝ) ≤ innerCutoff n := by exact_mod_cast hQ
  have hu : 0 < innerWidth n :=
    mul_pos (zero_lt_one.trans_le hQ') (Real.rpow_pos_of_pos hn0 _)
  have hu1 : 1 ≤ innerWidth n :=
    one_le_mul_of_one_le_of_one_le hQ' (Real.one_le_rpow hnR (by norm_num))
  have hQsmall : 384 * (Real.log (n : ℝ))^2 ≤ (n : ℝ)^(1/30 : ℝ) := by
    linarith
  have hwidth : 24 * innerWidth n ≤ (n : ℝ)^(1/5 : ℝ) := by
    have hs : 24 * (innerCutoff n : ℝ) ≤ (n : ℝ)^(1/30 : ℝ) := by
      linarith only [narrow_le_log n hn, hQsmall]
    calc
      _ = (24 * (innerCutoff n : ℝ)) * (n : ℝ)^(1/6 : ℝ) := by unfold innerWidth; ring
      _ ≤ (n : ℝ)^(1/30 : ℝ) * (n : ℝ)^(1/6 : ℝ) :=
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hdiv : 2 * (n : ℝ)^(4/5 : ℝ) ≤ (n : ℝ)/(12 * innerWidth n) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ = (24 * innerWidth n) * (n : ℝ)^(4/5 : ℝ) := by ring
      _ ≤ (n : ℝ)^(1/5 : ℝ) * (n : ℝ)^(4/5 : ℝ) :=
        mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hf := Nat.lt_floor_add_one ((n : ℝ)/(12 * innerWidth n))
  change (n : ℝ)/(12 * innerWidth n) < (innerWindow n : ℝ) + 1 at hf
  have h1 : 1 ≤ (n : ℝ)^(4/5 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have hfloor : (innerWindow n : ℝ) ≤ (n : ℝ)/(12 * innerWidth n) :=
    Nat.floor_le (by positivity)
  have hn' : (innerWindow n : ℝ) ≤ (n : ℝ) :=
    hfloor.trans (div_le_self hn0.le (by linarith))
  have hmul := (le_div_iff₀ (show 0 < 12 * innerWidth n by positivity)).1 hfloor
  exact ⟨by linarith, by exact_mod_cast hn', by nlinarith only [hmul, hn0]⟩

theorem sharpModulusBudget {n x h : ℕ} {t : ℝ} (hn : 1 ≤ n) (hx : 1 ≤ x)
    (hxn : x ≤ n) (hlo : (n : ℝ)^(4/5 : ℝ) ≤ (h : ℝ))
    (ht : (4/5 : ℝ) ≤ t) (ht' : t ≤ 1) :
    (outerCutoff n : ℝ)^2 * (x : ℝ)^((1-t)/3+1/16) ≤ (h : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxnR : (x : ℝ) ≤ n := by exact_mod_cast hxn
  have hB : (outerCutoff n : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hp : (x : ℝ)^((1-t)/3+1/16) ≤ (n : ℝ)^(31/240 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hxR (by linarith)).trans
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hxnR (by norm_num))
  calc
    _ ≤ ((n : ℝ)^(1/3 : ℝ))^2 * (n : ℝ)^(31/240 : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2) hp
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
    _ = (n : ℝ)^(191/240 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
      norm_num
    _ ≤ (n : ℝ)^(4/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
    _ ≤ _ := hlo

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFixedPowerBands.lean; sha256 9a869bc8a7ee62f43c97b6c87b3b9c5776f115bebca902b4927ef6fa27565b88 -/
section
/-!
Ten fixed exponent bands rather than O(log n) dyadic denominator bands.
The first lower denominator is at least the frozen narrow cutoff;
each subsequent endpoint is floor(n^(j/50)). A constant number of
bands is enough because the explicit-formula scale inequalities have
strict exponent slack even at the top endpoint 1/5.

This is only the parameter/partition step, not the zero-free theorem.
-/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def fixedBandLowerExp (j : ℕ) : ℝ := (j:ℝ)/50
def fixedBandUpperExp (j : ℕ) : ℝ := ((j+1:ℕ):ℝ)/50
def fixedBandWindowExp (j : ℕ) : ℝ :=
  min (5/6 + fixedBandLowerExp j - 1/100) (99/100)

def fixedBandEnd (n j : ℕ) : ℕ :=
  max (innerCutoff n) ⌊(n:ℝ)^(fixedBandLowerExp j)⌋₊

def fixedBandWindow (n j : ℕ) : ℕ :=
  ⌊(n:ℝ)^(fixedBandWindowExp j)⌋₊

/-- All relevant exponent inequalities have explicit slack. In particular,
the worst density scale is the last band and still saves 1/150. -/
theorem fixedBandExponents (j : ℕ) (hj : j < 10) (b : ℝ)
    (hb : fixedBandWindowExp j - 1/1000 ≤ b) (hb' : b ≤ 1) :
    0 ≤ fixedBandLowerExp j ∧
    fixedBandUpperExp j ≤ 1/5 ∧
    4/5+1/100 ≤ fixedBandWindowExp j ∧
    fixedBandWindowExp j ≤ 99/100 ∧
    fixedBandWindowExp j + 1/100 ≤ 5/6 + fixedBandLowerExp j ∧
    2*fixedBandUpperExp j+(7/12)*b-fixedBandWindowExp j ≤ -1/150 ∧
    fixedBandUpperExp j+(2/3)*b-fixedBandWindowExp j ≤ -1/10 ∧
    fixedBandUpperExp j-b/6-fixedBandWindowExp j ≤ -1/10 ∧
    3*fixedBandUpperExp j-b/6-fixedBandWindowExp j ≤ -1/10 ∧
    fixedBandUpperExp j+b/2-fixedBandWindowExp j ≤ -1/4 ∧
    fixedBandUpperExp j-b/2 ≤ -1/10 := by
  interval_cases j <;>
    norm_num [fixedBandLowerExp,fixedBandUpperExp,fixedBandWindowExp,min_def] at * <;>
    (repeat' (first | apply And.intro | linarith))

theorem fixedBandEnd_mono (n : ℕ) (hn : 1 ≤ n) :
    Monotone (fixedBandEnd n) := by
  intro j k hjk
  unfold fixedBandEnd
  apply max_le_max le_rfl
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  unfold fixedBandLowerExp
  gcongr

theorem fixedBandEnd_zero (n : ℕ) (hQ : 1 ≤ innerCutoff n) :
    fixedBandEnd n 0=innerCutoff n := by
  simp [fixedBandEnd,fixedBandLowerExp,max_eq_left hQ]

theorem fixedBandEnd_ten (n : ℕ) (hQA : innerCutoff n ≤ middleCutoff n) :
    fixedBandEnd n 10=middleCutoff n := by
  have he : fixedBandLowerExp 10=1/5 := by norm_num [fixedBandLowerExp]
  rw [fixedBandEnd,he]
  exact max_eq_right hQA

theorem fixedBandWindow_bounds (n j : ℕ) (hn : 1 ≤ n) (hj : j < 10) :
    fixedBandWindow n j ≤ n ∧
    (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^(99/100:ℝ) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc : fixedBandWindowExp j ≤ (99/100:ℝ) := min_le_right _ _
  have hf : (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hh := hf.trans (Real.rpow_le_rpow_of_exponent_le hn' hc)
  have hn'': (fixedBandWindow n j:ℝ) ≤ (n:ℝ) := hh.trans (by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hn' (show (99/100:ℝ) ≤ 1 by norm_num)))
  exact ⟨Nat.cast_le.mp hn'',hh⟩

/-- The ten widths all satisfy the exact Gallagher frequency condition
and the uniform lower bound needed for the principal prime window.
The cap n^.99 gives a polynomial boundary saving, not just a log cap. -/
theorem eventualFixedBandWindows : ∀ᶠ n : ℕ in atTop,
    ∀ j < 10,
      (n:ℝ)^(4/5:ℝ) ≤ (fixedBandWindow n j:ℝ) ∧
      (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^(99/100:ℝ) ∧
      6*(fixedBandWindow n j:ℝ)*innerWidth n ≤ (fixedBandEnd n j:ℝ)*n := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htiny := (tendsto_rpow_atTop (show (0:ℝ) < 1/100 by norm_num)).comp ht
  filter_upwards [eventualInnerGeometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/100) (1/192) (by norm_num) (by norm_num),
    htiny.eventually_ge_atTop 2] with n hg hlog hsmall
  intro j hj
  obtain ⟨hn,hQ,hQA,hAB,huH,hsep⟩ := hg
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hc : (4/5+1/100:ℝ) ≤ fixedBandWindowExp j := by
    unfold fixedBandWindowExp fixedBandLowerExp
    apply le_min <;> linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hres : fixedBandWindowExp j+1/100 ≤ 5/6+fixedBandLowerExp j := by
    unfold fixedBandWindowExp
    linarith only [min_le_left (5/6+fixedBandLowerExp j-1/100) (99/100:ℝ)]
  have hf := Nat.lt_floor_add_one ((n:ℝ)^fixedBandWindowExp j)
  change (n:ℝ)^fixedBandWindowExp j < (fixedBandWindow n j:ℝ)+1 at hf
  have hlower : 2*(n:ℝ)^(4/5:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j := by
    calc
      _ ≤ (n:ℝ)^(1/100:ℝ)*(n:ℝ)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hnP.le _)
      _ = (n:ℝ)^(4/5+1/100:ℝ) := by rw [← Real.rpow_add hnP]; congr 1 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR hc
  have h1 := Real.one_le_rpow hnR (show (0:ℝ) ≤ 4/5 by norm_num)
  have hf' : (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j :=
    Nat.floor_le (Real.rpow_nonneg hnP.le _)
  have hQlog : (innerCutoff n:ℝ) ≤ 16*(Real.log (n:ℝ))^2 := by
    -- Public re-use of the bound through the exact narrow definition.
    have hp : (2:ℝ)^Nat.log 2 (n+2) ≤ ((n+2:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2≠0)
    have hraw := Real.log_le_log (by positivity) hp
    have hin : ((n+2:ℕ):ℝ) ≤ (n:ℝ)^2 := by
      push_cast
      nlinarith only [(show (2:ℝ) ≤ n by exact_mod_cast hn),sq_nonneg ((n:ℝ)-2)]
    have hlog' := Real.log_le_log (by positivity) hin
    rw [Real.log_pow] at hraw hlog'
    have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2)))
    have hL : (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
      push_cast at hraw hlog'
      linarith only [hraw,hlog',hm]
    unfold innerCutoff GoldbachGRHBudget.narrow
    push_cast
    calc
      _ ≤ (4*Real.log n)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
      _ = _ := by ring
  have hQsmall : 12*(innerCutoff n:ℝ) ≤ (n:ℝ)^(1/100:ℝ) := by
    linarith only [hQlog,hlog]
  have hD : (n:ℝ)^fixedBandLowerExp j ≤ 2*(fixedBandEnd n j:ℝ) := by
    have hp := Nat.lt_floor_add_one ((n:ℝ)^fixedBandLowerExp j)
    have hm : (⌊(n:ℝ)^fixedBandLowerExp j⌋₊:ℝ) ≤ (fixedBandEnd n j:ℝ) := by
      exact_mod_cast le_max_right (innerCutoff n) ⌊(n:ℝ)^fixedBandLowerExp j⌋₊
    have hD1 : (1:ℝ) ≤ fixedBandEnd n j := by
      exact_mod_cast hQ.trans (le_max_left _ _)
    linarith
  refine ⟨by linarith,(fixedBandWindow_bounds n j (by omega) hj).2,?_⟩
  have hpow : (n:ℝ)^(fixedBandWindowExp j+1/100+1/6) ≤ (n:ℝ)^(1+fixedBandLowerExp j) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  calc
    _ = (12*(innerCutoff n:ℝ))*(fixedBandWindow n j:ℝ)*(n:ℝ)^(1/6:ℝ)/2 := by
      unfold innerWidth
      ring
    _ ≤ ((n:ℝ)^(1/100:ℝ)*(n:ℝ)^fixedBandWindowExp j)*(n:ℝ)^(1/6:ℝ)/2 := by
      gcongr
    _ = (n:ℝ)^(fixedBandWindowExp j+1/100+1/6)/2 := by
      rw [← Real.rpow_add hnP,← Real.rpow_add hnP]
      congr 2 <;> ring
    _ ≤ (n:ℝ)^(1+fixedBandLowerExp j)/2 :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    _ = (n:ℝ)*((n:ℝ)^fixedBandLowerExp j)/2 := by rw [Real.rpow_add hnP,Real.rpow_one]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hD hnP.le]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFixedBandAnalyticParameters.lean; sha256 925b2e6ba67302be5fe7afd03caf43c3a044ae782d91df5108ec50312718c0a1 -/
section
/-! Use global n-based smoothing and truncation parameters on all
integer dyadic blocks, avoiding an extra local log-scale parameter.
The endpoint exponent a and window exponent c have fixed slack.
No zero-free theorem is assumed or asserted in this file. -/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem fixedBandGlobalExponents (j : ℕ) (hj : j < 10) :
    let a := fixedBandUpperExp j
    let c := fixedBandWindowExp j
    1/50 ≤ a ∧ a ≤ 1/5 ∧ 4/5+1/100 ≤ c ∧
    2*a+7/12 ≤ c-1/150 ∧
    a+3/2 ≤ 2*c-1/10 ∧
    a+2/3 ≤ c-1/10 ∧
    a-1/6 ≤ c-1/10 ∧
    3*a-1/6 ≤ c-1/10 ∧
    a+1/2 ≤ c-1/4 := by
  dsimp only
  interval_cases j <;> norm_num [fixedBandUpperExp,fixedBandWindowExp,
    fixedBandLowerExp,min_def]

private theorem cutoff_log_square (n : ℕ) (hn : 2 ≤ n) :
    (innerCutoff n:ℝ) ≤ 16*(Real.log (n:ℝ))^2 := by
  have hp : (2:ℝ)^Nat.log 2 (n+2) ≤ ((n+2:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2≠0)
  have hraw := Real.log_le_log (by positivity) hp
  have hin : ((n+2:ℕ):ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [(show (2:ℝ) ≤ n by exact_mod_cast hn),sq_nonneg ((n:ℝ)-2)]
  have hlog' := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog'
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2)))
  have hL : (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
    push_cast at hraw hlog'
    linarith only [hraw,hlog',hm]
  unfold innerCutoff GoldbachGRHBudget.narrow
  push_cast
  calc
    _ ≤ (4*Real.log n)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
    _ = _ := by ring

theorem eventualFixedBandPowerEndpoints : ∀ᶠ n : ℕ in atTop,
    ∀ j < 10,
      1 ≤ fixedBandEnd n (j+1) ∧
      (fixedBandEnd n (j+1):ℝ) ≤ (n:ℝ)^fixedBandUpperExp j ∧
      (n:ℝ)^fixedBandWindowExp j ≤ 2*(fixedBandWindow n j:ℝ) := by
  filter_upwards [eventualInnerGeometry,eventualFixedBandWindows,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/100) (1/16) (by norm_num) (by norm_num)]
    with n hg hw hlog
  intro j hj
  obtain ⟨hn,hQ,hQA,hAB,huH,hsep⟩ := hg
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hQsmall : (innerCutoff n:ℝ) ≤ (n:ℝ)^(1/100:ℝ) :=
    (cutoff_log_square n hn).trans (by linarith only [hlog])
  have ha : (1/100:ℝ) ≤ fixedBandUpperExp j := by
    unfold fixedBandUpperExp
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hQpow := hQsmall.trans (Real.rpow_le_rpow_of_exponent_le hnR ha)
  have hfl : (⌊(n:ℝ)^fixedBandLowerExp (j+1)⌋₊:ℝ) ≤
      (n:ℝ)^fixedBandUpperExp j :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hA : 1 ≤ fixedBandEnd n (j+1) := hQ.trans (le_max_left _ _)
  have hh1 : (1:ℝ) ≤ fixedBandWindow n j :=
    (Real.one_le_rpow hnR (by norm_num : (0:ℝ) ≤ 4/5)).trans (hw j hj).1
  have hf := Nat.lt_floor_add_one ((n:ℝ)^fixedBandWindowExp j)
  change (n:ℝ)^fixedBandWindowExp j < (fixedBandWindow n j:ℝ)+1 at hf
  refine ⟨hA,?_,by linarith⟩
  unfold fixedBandEnd
  push_cast
  exact max_le hQpow hfl

def fixedTruncationIndex (n : ℕ) : ℕ := Nat.log 2 ⌊(n:ℝ)^(3/2:ℝ)⌋₊

theorem fixedTruncation_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(3/2:ℝ) ≤ (2:ℝ)^(fixedTruncationIndex n+1) ∧
    (2:ℝ)^(fixedTruncationIndex n+1) ≤ 2*(n:ℝ)^(3/2:ℝ) := by
  let R := (n:ℝ)^(3/2:ℝ)
  let m := ⌊R⌋₊
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hm : 1 ≤ m := Nat.le_floor (Real.one_le_rpow hnR (by norm_num))
  have hupper : (2:ℕ)^(Nat.log 2 m) ≤ m :=
    Nat.pow_log_le_self 2 (by omega)
  have hlower := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  have hf := Nat.lt_floor_add_one R
  have hF : (m:ℝ) ≤ R := Nat.floor_le (by dsimp [R]; positivity)
  have hu : (2:ℝ)^(Nat.log 2 m) ≤ (m:ℝ) := by exact_mod_cast hupper
  have hl : (m:ℝ)+1 ≤ (2:ℝ)^(Nat.log 2 m+1) := by
    exact_mod_cast (show m+1 ≤ 2^(Nat.log 2 m+1) by omega)
  change R ≤ (2:ℝ)^(Nat.log 2 m+1) ∧ (2:ℝ)^(Nat.log 2 m+1) ≤ 2*R
  constructor
  · exact hf.le.trans hl
  · rw [pow_succ]
    nlinarith only [hu,hF]

theorem fixedTruncation_logBound (n : ℕ) (hn : 2 ≤ n) :
    ((fixedTruncationIndex n+1:ℕ):ℝ) ≤ 5*Real.log (n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnP : (0:ℝ) < n := by linarith
  have hlog := Real.log_le_log (by positivity) (fixedTruncation_bounds n (by omega)).2
  rw [Real.log_pow,Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hnP _).ne',
    Real.log_rpow hnP] at hlog
  have hL2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL := Real.log_le_log (by norm_num : (0:ℝ) < 2) hnR
  have H := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg (fixedTruncationIndex n+1))
  nlinarith only [hlog,H,hL]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFixedBlockScale.lean; sha256 70e1ea66fa1c975653e1c542a2f22f205416ab7497f07c6f9441beab780b18bf -/
section
/-! All exact hypotheses of the primitive spectral block theorem from
the fixed exponent band parameters. Global smoothing delta=n^(2/3)
and dyadic truncation U~n^(3/2) work simultaneously for 2h<=X<=n. -/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

private theorem power_reserve {n e c d R : ℝ} (hn : 1 ≤ n)
    (hR : 0 ≤ R) (hsmall : R ≤ n^d) (he : e+d ≤ c) :
    R*n^e ≤ n^c := by
  have hnp : 0 < n := by linarith
  calc
    _ ≤ n^d*n^e := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hnp.le _)
    _ = n^(d+e) := (Real.rpow_add hnp d e).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by linarith)

theorem eventualFixedBlockScale :
    ∀ᶠ n : ℕ in atTop, ∀ j < 10, ∀ X : ℕ,
      let A := fixedBandEnd n (j+1)
      let h := fixedBandWindow n j
      let K := fixedTruncationIndex n
      let δ := (n:ℝ)^(2/3:ℝ)
      2*h ≤ X → X ≤ n →
      1 ≤ A ∧ 0 < h ∧ (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) ∧
      (h:ℝ) ≤ (X:ℝ)/2 ∧ 1 ≤ δ ∧ δ ≤ (X:ℝ)/2 ∧ A ≤ X ∧
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2)) ≤ ((X:ℝ)/2)^(5/12:ℝ) ∧
      (A:ℝ)^2/((h:ℝ)/(X:ℝ)) ≤ (X:ℝ)^(5/12:ℝ) ∧
      Real.log ((A:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log ((X:ℝ)/2) ∧
      (4/5:ℝ)*Real.log (n:ℝ) ≤ Real.log ((X:ℝ)/2) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, (8:ℝ) ≤ (n:ℝ)^(1/150:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/150)).comp ht).eventually
      (eventually_ge_atTop 8)
  filter_upwards [eventually_ge_atTop (2:ℕ), eventualFixedBandWindows,
    eventualFixedBandPowerEndpoints,hsmall] with n hn hw he hp
  intro j hj X
  dsimp only
  intro hhX hXn
  let A := fixedBandEnd n (j+1)
  let h := fixedBandWindow n j
  let K := fixedTruncationIndex n
  let a := fixedBandUpperExp j
  let c := fixedBandWindowExp j
  let δ := (n:ℝ)^(2/3:ℝ)
  let U := (2:ℝ)^(K+1)
  obtain ⟨hA,hAp,hcp⟩ := he j hj
  obtain ⟨hhlo,hhhi,hwidth⟩ := hw j hj
  obtain ⟨ha,ha',hc,hdens,hUexp,hδexp,hneg,hcub,hpp⟩ := fixedBandGlobalExponents j hj
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hA0 : (0:ℝ) < A := by exact_mod_cast (show 0 < fixedBandEnd n (j+1) by omega)
  have hhP : (0:ℝ) < h :=
    (Real.rpow_pos_of_pos hnP (4/5:ℝ)).trans_le hhlo
  have hhN : 0 < h := Nat.cast_pos.mp hhP
  have hhX' : (h:ℝ) ≤ (X:ℝ)/2 := by
    have H : (2:ℝ)*(h:ℝ) ≤ X := by exact_mod_cast hhX
    linarith only [H]
  have hXP : (0:ℝ) < X := by linarith only [hhP,hhX']
  have hXn' : (X:ℝ) ≤ n := by exact_mod_cast hXn
  have hh1 : 1 ≤ (h:ℝ) := (Real.one_le_rpow hnR (by norm_num : (0:ℝ) ≤ 4/5)).trans hhlo
  have hXhalf1 : 1 ≤ (X:ℝ)/2 := hh1.trans hhX'
  have hp' : (8:ℝ) ≤ (n:ℝ)^(1/100:ℝ) :=
    hp.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have hlarge : 4*(n:ℝ)^(4/5:ℝ) ≤ (n:ℝ)^c :=
    power_reserve hnR (by norm_num) (by linarith : (4:ℝ) ≤ (n:ℝ)^(1/100:ℝ))
      (by exact hc)
  have hh4 : 2*(n:ℝ)^(4/5:ℝ) ≤ (h:ℝ) := by linarith only [hlarge,hcp]
  have hlow : (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) := by
    calc
      _ ≤ (2*(n:ℝ))^(4/5:ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2:ℝ)^(4/5:ℝ)*(n:ℝ)^(4/5:ℝ) := Real.mul_rpow (by norm_num) hnP.le
      _ ≤ 2*(n:ℝ)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (4/5:ℝ) ≤ 1))
          (Real.rpow_nonneg hnP.le _)
      _ ≤ _ := hh4
  have hδ1 : 1 ≤ δ := Real.one_le_rpow hnR (by norm_num)
  have hδh : δ ≤ (h:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (2/3:ℝ) ≤ 4/5)).trans hhlo
  have hAX : (A:ℝ) ≤ X := calc
    _ ≤ (n:ℝ)^a := hAp
    _ ≤ (n:ℝ)^(4/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [ha'])
    _ ≤ h := hhlo
    _ ≤ _ := by linarith only [hhX',hhP]
  have hds (Y : ℝ) (hY : 0 < Y) (hYn : Y ≤ n) :
      (A:ℝ)^2/((h:ℝ)/Y) ≤ Y^(5/12:ℝ) := by
    have hprod : (A:ℝ)^2*Y^(7/12:ℝ) ≤ (h:ℝ) := by
      calc
        _ ≤ ((n:ℝ)^a)^2*(n:ℝ)^(7/12:ℝ) :=
          mul_le_mul (pow_le_pow_left₀ hA0.le hAp 2)
            (Real.rpow_le_rpow hY.le hYn (by norm_num))
            (Real.rpow_nonneg hY.le _) (sq_nonneg _)
        _ = (n:ℝ)^(2*a+7/12) := by
          rw [pow_two,← Real.rpow_add hnP,← Real.rpow_add hnP]
          congr 1 <;> ring
        _ ≤ (h:ℝ) := by
          have H : 2*(n:ℝ)^(2*a+7/12) ≤ (n:ℝ)^c :=
            power_reserve hnR (by norm_num) (by linarith : (2:ℝ) ≤ (n:ℝ)^(1/150:ℝ))
              (by linarith only [hdens])
          linarith only [H,hcp]
    apply (div_le_iff₀ (div_pos hhP hY)).2
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hY).2
    have H := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hY.le (5/12:ℝ))
    rw [mul_assoc,← Real.rpow_add hY,show (7/12:ℝ)+5/12=1 by norm_num,Real.rpow_one] at H
    simpa only [mul_div_assoc,mul_comm,mul_left_comm] using H
  have hUcap : U ≤ 2*(n:ℝ)^(3/2:ℝ) := (fixedTruncation_bounds n (by omega)).2
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hproduct : (A:ℝ)*U ≤ ((X:ℝ)/2)^2 := by
    have hreserve : 8*(n:ℝ)^(a+3/2) ≤ (n:ℝ)^(2*c) :=
      power_reserve hnR (by norm_num)
        (hp.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1/150:ℝ) ≤ 1/10)))
        (by linarith only [hUexp])
    have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hnP.le c) hcp 2
    rw [pow_two,← Real.rpow_add hnP,show c+c=2*c by ring] at hsq
    have hsq' : (n:ℝ)^(2*c) ≤ 4*(h:ℝ)^2 := by nlinarith only [hsq]
    calc
      _ ≤ (n:ℝ)^a*(2*(n:ℝ)^(3/2:ℝ)) :=
        mul_le_mul hAp hUcap hUpos.le (Real.rpow_nonneg hnP.le a)
      _ = 2*(n:ℝ)^(a+3/2) := by rw [← mul_assoc,mul_comm ((n:ℝ)^a) 2,mul_assoc,← Real.rpow_add hnP]
      _ ≤ (h:ℝ)^2 := by linarith only [hreserve,hsq']
      _ ≤ _ := pow_le_pow_left₀ hhP.le hhX' 2
  have hlog := Real.log_le_log (mul_pos hA0 hUpos) hproduct
  rw [Real.log_pow] at hlog
  have hloglow := Real.log_le_log (Real.rpow_pos_of_pos hnP (4/5:ℝ)) (hhlo.trans hhX')
  rw [Real.log_rpow hnP] at hloglow
  refine ⟨hA,hhN,hlow,hhX',hδ1,hδh.trans hhX',Nat.cast_le.mp hAX,
    hds ((X:ℝ)/2) (by linarith) (by linarith only [hXn',hXP]),
    hds X hXP hXn',?_,hloglow⟩
  simpa only [Nat.cast_ofNat,U,K,A] using hlog

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGlobalSmoothingBudget.lean; sha256 e44553463f83b5df26eb41af89d20a628b84011427f7add597ff68f6acd0f9ef -/
section
/-! Global n-based delta and U give an explicit polynomial saving
for the prime-power and smoothed explicit-formula remainders. -/
open Filter
open scoped Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem globalSmoothingBudget
    {n X A h U a c D : ℝ}
    (hn : 3 ≤ n) (hX : 1 ≤ X) (hXn : X ≤ n)
    (hA1 : 1 ≤ A) (hh : 0 < h) (hD : 0 < D)
    (hAp : A ≤ n^a) (hcp : n^c ≤ 2*h)
    (hU : n^(3/2:ℝ) ≤ U)
    (hlog : Real.log (A*U) ≤ 2*Real.log n)
    (he₁ : a+2/3 ≤ c-1/10)
    (he₂ : a-1/6 ≤ c-1/10)
    (he₃ : 3*a-1/6 ≤ c-1/10)
    (he₄ : a+1/2 ≤ c-1/4) :
    let δ := n^(2/3:ℝ)
    let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        A^2*X^2*Real.log (A*U)/(δ*U))+
          2*Real.sqrt (3*X)*Real.log (3*X)
    A*E ≤ (8*D+16)*h*n^(-(1/10):ℝ)*Real.log n := by
  dsimp only
  let δ := n^(2/3:ℝ)
  let L := Real.log n
  let r := n^(-(1/10):ℝ)
  have hnP : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hA : 0 < A := by linarith
  have hδ : 0 < δ := Real.rpow_pos_of_pos hnP _
  have hr : 0 < r := Real.rpow_pos_of_pos hnP _
  have hU0 : 0 < U := (Real.rpow_pos_of_pos hnP _).trans_le hU
  have hL : 0 ≤ L := Real.log_nonneg hn1
  have hLX : Real.log X ≤ L := Real.log_le_log (by linarith) hXn
  have hLX0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hL3 : Real.log (3*X) ≤ 2*L := by
    have H := Real.log_le_log (by linarith : 0 < 3*X)
      (show 3*X ≤ n^2 by nlinarith only [hXn,hn,mul_le_mul_of_nonneg_right hn (show 0 ≤ n by positivity)])
    rw [Real.log_pow] at H
    norm_num at H
    exact H
  have hL30 : 0 ≤ Real.log (3*X) := Real.log_nonneg (by linarith)
  have hreserve (e : ℝ) (he : e ≤ c-1/10) : n^e ≤ 2*h*r := by
    calc
      _ ≤ n^(c-1/10) := Real.rpow_le_rpow_of_exponent_le hn1 he
      _ = n^c*r := by dsimp [r]; rw [← Real.rpow_add hnP]; congr 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcp hr.le
  have hroot : Real.sqrt X ≤ n^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hXn
  have hroot3 : Real.sqrt (3*X) ≤ 2*n^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    have hs : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
    exact mul_le_mul hs (Real.sqrt_le_sqrt hXn) (Real.sqrt_nonneg _) (by norm_num)
  have h1 : A*δ ≤ 2*h*r := by
    calc
      _ ≤ n^a*n^(2/3:ℝ) := mul_le_mul_of_nonneg_right hAp hδ.le
      _ = n^(a+2/3) := (Real.rpow_add hnP _ _).symm
      _ ≤ _ := hreserve _ he₁
  have h2 : A*Real.sqrt X/δ ≤ 2*h*r := by
    calc
      _ ≤ n^a*n^(1/2:ℝ)/δ :=
        div_le_div_of_nonneg_right
          (mul_le_mul hAp hroot (Real.sqrt_nonneg _) (Real.rpow_nonneg hnP.le _)) hδ.le
      _ = n^(a-1/6) := by
        dsimp [δ]
        rw [← Real.rpow_add hnP,← Real.rpow_sub hnP]
        congr 1 <;> ring
      _ ≤ _ := hreserve _ he₂
  have h3 : A^3*X^2/(δ*U) ≤ 2*h*r := by
    have hden : n^(2/3:ℝ)*n^(3/2:ℝ) ≤ δ*U :=
      mul_le_mul_of_nonneg_left hU hδ.le
    calc
      _ ≤ (n^a)^3*n^2/(n^(2/3:ℝ)*n^(3/2:ℝ)) := by
        apply le_trans (div_le_div_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ hA.le hAp 3)
            (pow_le_pow_left₀ (by linarith) hXn 2) (sq_nonneg _) (by positivity))
          (mul_nonneg hδ.le hU0.le))
        exact div_le_div_of_nonneg_left (by positivity)
          (mul_pos (Real.rpow_pos_of_pos hnP _) (Real.rpow_pos_of_pos hnP _)) hden
      _ = n^(3*a-1/6) := by
        rw [← Real.rpow_add hnP,show (n^a)^3=n^(3*a) by
          rw [← Real.rpow_natCast,← Real.rpow_mul hnP.le]
          norm_num; congr 1 <;> ring,
          ← Real.rpow_natCast,← Real.rpow_add hnP,← Real.rpow_sub hnP]
        congr 1 <;> ring
      _ ≤ _ := hreserve _ he₃
  have h4 : A*Real.sqrt (3*X) ≤ 4*h*r := by
    calc
      _ ≤ n^a*(2*n^(1/2:ℝ)) :=
        mul_le_mul hAp hroot3 (Real.sqrt_nonneg _) (Real.rpow_nonneg hnP.le _)
      _ = 2*n^(a+1/2) := by rw [← mul_assoc,mul_comm (n^a) 2,mul_assoc,← Real.rpow_add hnP]
      _ ≤ 2*(2*h*r) := mul_le_mul_of_nonneg_left (hreserve _ (by linarith only [he₄])) (by norm_num)
      _ = _ := by ring
  have b1 := mul_le_mul h1 hLX hLX0 (by positivity : 0 ≤ 2*h*r)
  have b2 := mul_le_mul h2 hLX hLX0 (by positivity : 0 ≤ 2*h*r)
  have b3 := mul_le_mul h3 hlog
    (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hA1
      ((Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 3/2)).trans hU)))
    (by positivity : 0 ≤ 2*h*r)
  have b4 := mul_le_mul h4 hL3 hL30 (by positivity : 0 ≤ 4*h*r)
  change A*(D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
      A^2*X^2*Real.log (A*U)/(δ*U))+
      2*Real.sqrt (3*X)*Real.log (3*X)) ≤ (8*D+16)*h*r*L
  have hsum :
      (A*δ)*Real.log X+(A*Real.sqrt X/δ)*Real.log X+
      (A^3*X^2/(δ*U))*Real.log (A*U) ≤ 8*h*r*L := by
    linarith only [b1,b2,b3]
  have H := mul_le_mul_of_nonneg_left hsum hD.le
  have H4 := mul_le_mul_of_nonneg_left b4 (show (0:ℝ) ≤ 2 by norm_num)
  convert add_le_add H H4 using 1 <;> ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorBlockScalarBudget.lean; sha256 8546a0b58def1ad72598c9fcbf1c535d9fb2d7bc069767ed08fe3288507b14ce -/
section
/-! Scalar assembly of the explicit-formula residual, good-zero energy
and principal energy. The only large parameter is the global logarithm L. -/
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem logDenominatorBudget {L l : ℝ} (hL : 0 < L) (hl : L/2 ≤ l) (k : ℕ) :
    1/l^k ≤ (2:ℝ)^k/L^k := by
  have hlp : 0 < l := by linarith
  apply (div_le_div_iff₀ (pow_pos hlp _) (pow_pos hL _)).2
  have hp : L^k ≤ (2*l)^k := pow_le_pow_left₀ hL.le (by linarith) _
  rw [mul_pow] at hp
  simpa only [one_mul] using hp

theorem blockScalarBudget {n X A h E K D C P L l₁ l₂ : ℝ}
    (hn : 1 ≤ n) (hX : 0 ≤ X) (hA : 0 ≤ A) (hh : 0 ≤ h)
    (hE : 0 ≤ E) (hK : 0 ≤ K) (hD : 0 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hL : 0 < L) (h₁ : L/2 ≤ l₁) (h₂ : L/2 ≤ l₂)
    (hk : K ≤ 5*L)
    (he : A*E ≤ (8*D+16)*h*n^(-(1/10):ℝ)*L)
    (hsmall : L^10 ≤ n^(1/5:ℝ)) :
    2*X*A^2*E^2 + 2*C*K^2*h^2*(X/2)/l₁^10 +
      2*C*K^2*h^2*X/l₂^10 + P*h^2*X/l₂^8 ≤
      (2*(8*D+16)^2+76800*C+256*P)*h^2*X/L^8 := by
  have hnP : 0 < n := by linarith
  have h₁p : 0 < l₁ := by linarith
  have h₂p : 0 < l₂ := by linarith
  have hp := pow_le_pow_left₀ (mul_nonneg hA hE) he 2
  have hr : (n^(-(1/10):ℝ))^2 = n^(-(1/5):ℝ) := by
    rw [pow_two,← Real.rpow_add hnP]
    congr 1 <;> ring
  have haux : n^(-(1/5):ℝ)*L^10 ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnP.le (-(1/5):ℝ))
    rw [← Real.rpow_add hnP,show -(1/5:ℝ)+1/5=0 by ring,Real.rpow_zero] at H
    exact H
  have herror : (A*E)^2 ≤ (8*D+16)^2*h^2/L^8 := by
    apply (le_div_iff₀ (pow_pos hL _)).2
    calc
      _ ≤ ((8*D+16)*h*n^(-(1/10):ℝ)*L)^2*L^8 :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = ((8*D+16)^2*h^2)*(n^(-(1/5):ℝ)*L^10) := by
        simp only [mul_pow,hr]
        ring
      _ ≤ _ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left haux (show 0 ≤ (8*D+16)^2*h^2 by positivity)
  have hk' : K^2 ≤ 25*L^2 := by
    calc
      _ ≤ (5*L)^2 := pow_le_pow_left₀ hK hk 2
      _ = _ := by ring
  have hnorm (l : ℝ) (hl : L/2 ≤ l) :
      K^2/l^10 ≤ 25600/L^8 := by
    have hlp : 0 < l := by linarith
    have H := logDenominatorBudget hL hl 10
    norm_num at H
    calc
      _ ≤ (25*L^2)*(1024/L^10) := by
        rw [div_eq_mul_inv]
        apply mul_le_mul hk' _ (by positivity) (by positivity)
        simpa only [one_div] using H
      _ = _ := by field_simp; ring
  have hPden := logDenominatorBudget hL h₂ 8
  norm_num at hPden
  have t1 := mul_le_mul_of_nonneg_left herror (show 0 ≤ 2*X by positivity)
  have t2 := mul_le_mul_of_nonneg_left (hnorm l₁ h₁)
    (show 0 ≤ C*h^2*X by positivity)
  have t3 := mul_le_mul_of_nonneg_left (hnorm l₂ h₂)
    (show 0 ≤ 2*C*h^2*X by positivity)
  have t4 := mul_le_mul_of_nonneg_left hPden (show 0 ≤ P*h^2*X by positivity)
  convert add_le_add (add_le_add (add_le_add t1 t2) t3) t4 using 1 <;> ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorUniformBlockLogEight.lean; sha256 0422183f72777132c185ecb2d082030679e2b6e57937eff80034f184d205e248 -/
section
/-! Conditional uniform arithmetic block theorem. All scale choices
and logarithmic losses are explicit. The only unproved hypothesis is
DirichletUniformStrip σ, σ<1. -/
open Filter Finset OAI.Ostmann
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem uniformStrip_fixedBandBlockLogEight {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j < 10, ∀ X : ℕ,
      let A := fixedBandEnd n (j+1)
      let h := fixedBandWindow n j
      2*h ≤ X → X ≤ n →
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        M*(h:ℝ)^2*(X:ℝ)/(Real.log n)^8 := by
  obtain ⟨D,C,P,hD,hC,hP,X₀,hX₀,hbound⟩ :=
    actualPrimitiveBlockOfUniformStrip hσ hs 10
  let M := 2*(8*D+16)^2+76800*C+256*P
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbig : ∀ᶠ n : ℕ in atTop, X₀ ≤ (n:ℝ)^(4/5:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 4/5)).comp ht).eventually
      (eventually_ge_atTop X₀)
  filter_upwards [eventually_ge_atTop (4:ℕ),eventualFixedBandWindows,
    eventualFixedBandPowerEndpoints,eventualFixedBlockScale,hbig,
    GoldbachGRHBudget.eventually_log_pow_le 10 (1/5) 1 (by norm_num) (by norm_num)]
    with n hn hw hp hscale hbig hsmall
  intro j hj X
  dsimp only
  intro hhX hXn
  let A := fixedBandEnd n (j+1)
  let h := fixedBandWindow n j
  let K := fixedTruncationIndex n
  let δ := (n:ℝ)^(2/3:ℝ)
  let U := (2:ℝ)^(K+1)
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
  obtain ⟨hA,hh,hlow,hhX',hδ1,hδX,hAX,hds₁,hds₂,hlog,hloglow⟩ :=
    hscale j hj X hhX hXn
  obtain ⟨_,hAp,hcp⟩ := hp j hj
  obtain ⟨hhlo,_,_⟩ := hw j hj
  obtain ⟨_,_,_,_,_,he₁,he₂,he₃,he₄⟩ := fixedBandGlobalExponents j hj
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hX0' : X₀ ≤ (X:ℝ) := by
    have H := hbig.trans hhlo
    linarith only [H,hhX',hhR]
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hXn' : (X:ℝ) ≤ n := by exact_mod_cast hXn
  have hA1 : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hUlo : (n:ℝ)^(3/2:ℝ) ≤ U := (fixedTruncation_bounds n (by omega)).1
  have hU1 : 1 ≤ U :=
    (Real.one_le_rpow (by linarith : (1:ℝ) ≤ n) (by norm_num)).trans hUlo
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hLhalf : Real.log (n:ℝ)/2 ≤ Real.log ((X:ℝ)/2) := by linarith
  have hLhalfpos : 0 < (X:ℝ)/2 := by linarith only [hhR,hhX']
  have hLhalf_le : Real.log ((X:ℝ)/2) ≤ Real.log (n:ℝ) :=
    Real.log_le_log hLhalfpos (by linarith)
  have hLfull : Real.log (n:ℝ)/2 ≤ Real.log (X:ℝ) :=
    hLhalf.trans (Real.log_le_log hLhalfpos (by linarith))
  have hlog' : Real.log ((A:ℝ)*U) ≤ 2*Real.log n := by
    linarith only [hlog,hLhalf_le]
  have hLx : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg hX1
  have hL3 : 0 ≤ Real.log (3*(X:ℝ)) := Real.log_nonneg (by linarith)
  have hLAU : 0 ≤ Real.log ((A:ℝ)*U) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hA1 hU1)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have herror : (A:ℝ)*E ≤ (8*D+16)*(h:ℝ)*(n:ℝ)^(-(1/10):ℝ)*Real.log n :=
    globalSmoothingBudget hnR hX1 hXn' hA1 hhR hD hAp hcp hUlo hlog'
      he₁ he₂ he₃ he₄
  have hscalar := blockScalarBudget
    (show (1:ℝ) ≤ n by linarith) (Nat.cast_nonneg (α:=ℝ) X)
    (Nat.cast_nonneg (α:=ℝ) A) hhR.le hE
    (Nat.cast_nonneg (α:=ℝ) (K+1)) hD.le hC.le hP.le hL hLhalf hLfull
    (fixedTruncation_logBound n (by omega)) herror (by simpa only [one_mul] using hsmall)
  have H := hbound A X h K δ hA hX0' hh hlow hhX' hδ1 hδX hAX hds₁ hds₂ hlog
  dsimp only at H
  exact H.trans (by simpa only [M,E,δ,U,K,A,h] using hscalar)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorSignedSparsePacket.lean; sha256 ffc13794634561ec41ad24fcda9ffafb5c4ad2967d4c0e926183d94bd65765d7 -/
section
/-!
Signed sparse character packets: exact Gauss expansion, conductor-sensitive
bounds, and the genuine divisibility obstruction. These are algebraic
lemmas, not assertions about the distribution of Dirichlet L-zeros.
-/

open Finset
open scoped Classical
open DyadicMixedB4CharacterFactorBound
open Conjectures.Goldbach.ReflectionCharacterContraction_aux
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1200000

variable {q : ℕ} [NeZero q]

def signedCharacterPacket (n : ZMod q)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ,
    (∑ χ ∈ S, w χ * χ (a : ZMod q))^2 *
      ZMod.stdAddChar (-n * (a : ZMod q))

/-- The signed quadratic expression uses the PRODUCT character, not the
conjugate-product appearing in ordinary Parseval. -/
theorem signedCharacterPacket_eq (n : ZMod q)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) :
    signedCharacterPacket n S w =
      ∑ χ ∈ S, ∑ ψ ∈ S,
        (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-n)) := by
  unfold signedCharacterPacket
  have he (a : (ZMod q)ˣ) :
      (∑ χ∈S,w χ*χ (a:ZMod q))^2 * ZMod.stdAddChar (-n*(a:ZMod q)) =
        ∑ χ∈S, ∑ ψ∈S,
          (w χ*w ψ)*((χ*ψ) (a:ZMod q) * ZMod.stdAddChar (-n*(a:ZMod q))) := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,MulChar.mul_apply]
    apply sum_congr rfl
    intro χ _
    apply sum_congr rfl
    intro ψ _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro χ _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro ψ _
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_units_eq_sum (fun a : ZMod q =>
    (χ*ψ) a * ZMod.stdAddChar (-n*a))
    (fun a ha => by rw [MulChar.map_nonunit _ ha,zero_mul])]
  unfold gaussSum
  simp only [AddChar.mulShift_apply]

/-- An unconditional divisor-sensitive bound for arbitrary n>0. -/
theorem signedCharacterPacket_divisorBound (n : ℕ) (hn : 0<n)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) :
    ‖signedCharacterPacket (n:ZMod q) S w‖ ≤
      ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*
        (Real.sqrt (χ*ψ).conductor *
          ∑ f∈n.divisors.filter (fun f => (χ*ψ).conductor*f ∣ q), (f:ℝ)) := by
  rw [signedCharacterPacket_eq]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro χ _
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro ψ _
  simp only [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_gauss_neg_shift_le (χ*ψ) (n:ZMod q)).trans
    (by simpa only [DirichletCharacter.changeLevel_self] using
      norm_dirichlet_gauss_induced (dvd_refl q) (χ*ψ) n hn)

/-- When n is a unit modulo q, every packet entry enjoys square-root
Gauss cancellation, including all imprimitive characters. -/
theorem norm_gauss_unit_shift (n : ℕ) (hnq : n.Coprime q)
    (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt q := by
  let u := ZMod.unitOfCoprime n hnq
  have hu : (u:ZMod q) = (n:ZMod q) := ZMod.coe_unitOfCoprime n hnq
  apply (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
  rw [← hu,gaussSum_mulShift_eq χ ZMod.stdAddChar u,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans
  exact (norm_dirichlet_gauss_standard χ).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level))

theorem signedCharacterPacket_unitBound (n : ℕ) (hnq : n.Coprime q)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) :
    ‖signedCharacterPacket (n:ZMod q) S w‖ ≤
      Real.sqrt q*(∑ χ∈S,‖w χ‖)^2 := by
  rw [signedCharacterPacket_eq]
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*Real.sqrt q := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro ψ _
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_gauss_unit_shift n hnq (χ*ψ)) (by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

/-- The unit-shift estimate for the actual Gauss-normalized Fourier
synthesis. At modulus q this saves q^{-1/2} up to totient losses, compared
to the worst-case unnormalized quadratic energy. -/
theorem normalizedSignedPacket_unitBound (n : ℕ) (hnq : n.Coprime q)
    (S : Finset (DirichletCharacter ℂ q))
    (F : DirichletCharacter ℂ q → ℂ) :
    ‖signedCharacterPacket (n:ZMod q) S
      (fun χ => gaussSum χ⁻¹ ZMod.stdAddChar*F χ/(q.totient:ℂ))‖ ≤
      Real.sqrt q*(Real.sqrt q/(q.totient:ℝ))^2*(∑ χ∈S,‖F χ‖)^2 := by
  let w (χ : DirichletCharacter ℂ q) :=
    gaussSum χ⁻¹ ZMod.stdAddChar*F χ/(q.totient:ℂ)
  have hw (χ : DirichletCharacter ℂ q) :
      ‖w χ‖ ≤ (Real.sqrt q/(q.totient:ℝ))*‖F χ‖ := by
    unfold w
    rw [norm_div,norm_mul,Complex.norm_natCast]
    have hg := norm_dirichlet_gauss_standard χ⁻¹
    rw [DirichletCharacter.conductor_inv] at hg
    have hd : (χ.conductor:ℝ)≤q := by
      exact_mod_cast (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
    have hq := Real.sqrt_le_sqrt hd
    calc
      _ ≤ (Real.sqrt q*‖F χ‖)/(q.totient:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hg.trans hq)
          (norm_nonneg _)) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hs : (∑ χ∈S,‖w χ‖) ≤ (Real.sqrt q/(q.totient:ℝ))*(∑ χ∈S,‖F χ‖) := by
    rw [mul_sum]
    exact sum_le_sum fun χ _ => hw χ
  calc
    _ ≤ Real.sqrt q*(∑ χ∈S,‖w χ‖)^2 := signedCharacterPacket_unitBound n hnq S w
    _ ≤ Real.sqrt q*((Real.sqrt q/(q.totient:ℝ))*(∑ χ∈S,‖F χ‖))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ => norm_nonneg _) hs 2)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- A one-character packet already has a negative real signed energy
when the shift vanishes modulo q. This rules out relying on generic
sparsity or positivity of the signed quadratic form alone. -/
theorem signedCharacterPacket_negativeDirection
    (χ : DirichletCharacter ℂ q) (hχ : χ*χ=1) (c : ℝ) :
    (signedCharacterPacket (0:ZMod q) {χ} (fun _ => (c:ℂ)*Complex.I)).re =
      -(q.totient:ℝ)*c^2 := by
  rw [signedCharacterPacket_eq]
  simp only [sum_singleton,hχ,neg_zero]
  have hg : gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (0:ZMod q)) =
      ((q.totient:ℝ):ℂ) := by
    unfold gaussSum
    simp only [AddChar.mulShift_apply,zero_mul,AddChar.map_zero_eq_one,mul_one]
    rw [MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient,totient_cast]
  rw [hg]
  simp [Complex.mul_re,Complex.mul_im]
  ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorProductConductor.lean; sha256 42f48923c8bee33e34e0555986bd3707a43afef37e4f7fe18237040ff10602b5 -/
section
/-!
A product-conductor saving for arbitrary shifts, including noncoprime
shifts. The low-product-conductor packet is kept separate.
-/
open Finset
open scoped Classical
open DyadicMixedB4CharacterFactorBound
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem divisorSum_le_log (m : ℕ) (hm : 0 < m) :
    (∑ f ∈ m.divisors, (f:ℝ)) ≤ (m:ℝ)*(1+Real.log m) := by
  have hsub : m.divisors ⊆ Icc 1 m := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)⟩
  have hh : (∑ i∈Icc 1 m,(i:ℝ)⁻¹) ≤ 1+Real.log m := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_le_one_add_log m
  calc
    _ = ∑ ab∈m.divisorsAntidiagonal,(ab.1:ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => (a:ℝ))]
    _ = ∑ ab∈m.divisorsAntidiagonal,(m:ℝ)*(ab.2:ℝ)⁻¹ := by
      apply sum_congr rfl
      intro ab hab
      have hp := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have hb : ab.2 ≠ 0 := by
        intro hb
        rw [hb,mul_zero] at hp
        omega
      have he : (ab.1:ℝ)*(ab.2:ℝ)=(m:ℝ) := by exact_mod_cast hp
      rw [← he]
      field_simp
    _ = (m:ℝ)*(∑ f∈m.divisors,(f:ℝ)⁻¹) := by
      rw [← mul_sum,Nat.sum_divisorsAntidiagonal' (fun _ b => (b:ℝ)⁻¹)]
    _ ≤ (m:ℝ)*(∑ f∈Icc 1 m,(f:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

variable {q : ℕ} [NeZero q]

/-- Even when the shift is not invertible modulo q, the shifted Gauss sum
is at most q (1+log q) / sqrt(conductor). -/
theorem shiftedGauss_productConductor (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt χ.conductor := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hdp
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hmp
  have hqR : (q:ℝ)=(d:ℝ)*(m:ℝ) := by exact_mod_cast hm
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ m.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left hdp hdiv,hmp.ne'⟩
  have hmq : m ≤ q := by
    rw [hm]
    exact Nat.le_mul_of_pos_left _ hdp
  have hlog : Real.log m≤Real.log q :=
    Real.log_le_log hmR (by exact_mod_cast hmq)
  have hs : (Real.sqrt (d:ℝ))^2=(d:ℝ) := Real.sq_sqrt hdR.le
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hdR
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
      (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
        (by simpa only [DirichletCharacter.changeLevel_self,d] using
          norm_dirichlet_gauss_induced (dvd_refl q) χ n hn)
    _ ≤ Real.sqrt d*(∑ f∈m.divisors,(f:ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log m)) :=
      mul_le_mul_of_nonneg_left (divisorSum_le_log m hmp) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log q)) := by gcongr
    _ = _ := by
      change Real.sqrt (d:ℝ)*((m:ℝ)*(1+Real.log q)) =
        (q:ℝ)*(1+Real.log q)/Real.sqrt (d:ℝ)
      apply (eq_div_iff hroot.ne').2
      calc
        _ = (Real.sqrt (d:ℝ))^2 * ((m:ℝ)*(1+Real.log q)) := by ring
        _ = (d:ℝ)*((m:ℝ)*(1+Real.log q)) := by rw [hs]
        _ = _ := by rw [hqR]; ring

/-- The high-product-conductor part of the signed quadratic form has a
uniform square-root saving, independent of gcd(n,q). -/
theorem highProductConductorPacketBound
    (n : ℕ) (hn : 0 < n) (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) (hD : 0 < D) :
    ‖∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor),
       (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      ((q:ℝ)*(1+Real.log q)/Real.sqrt D)*(∑ χ∈S,‖w χ‖)^2 := by
  let K := (q:ℝ)*(1+Real.log q)/Real.sqrt D
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hL : 0≤(q:ℝ)*(1+Real.log q) := by
    have := Real.log_nonneg hq1
    positivity
  have hK : 0≤K := div_nonneg hL (Real.sqrt_nonneg _)
  have hterm (χ ψ : DirichletCharacter ℂ q) (hψ : D≤(χ*ψ).conductor) :
      ‖(w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
        ‖w χ‖*‖w ψ‖*K := by
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (shiftedGauss_productConductor (χ*ψ) n hn).trans
    exact div_le_div_of_nonneg_left hL (Real.sqrt_pos.2 (by exact_mod_cast hD))
      (Real.sqrt_le_sqrt (by exact_mod_cast hψ))
  change _ ≤ K*(∑ χ∈S,‖w χ‖)^2
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor), ‖w χ‖*‖w ψ‖*K := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      exact sum_le_sum fun ψ hψ => hterm χ ψ (mem_filter.mp hψ).2
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*K :=
      sum_le_sum fun χ _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorProductFamily.lean; sha256 f03dc1f3a8d78662c696e46e04d34af491645f58b0a6bb8dca16b52780d6d1d4 -/
section
/-!
Aggregate high-product-conductor weights over all common multiples.
Only finite arithmetic and the verified Gauss bound are used.
-/
open Finset InnerFloorLinearTotient
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem commonMultipleTotientWeight (A L : ℕ) (hL : 0 < L) (hLA : L ≤ A) :
    (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) ≤
      (weightConstant*(1+Real.log A))^2 := by
  let F (d : ℕ) : ℝ := if d=L then L else 0
  have hF : ∀ d, 0≤F d := by intro d; dsimp [F]; split_ifs <;> positivity
  have hA : 0 < A := hL.trans_le hLA
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by exact_mod_cast hA)
  have hlogL : Real.log L ≤ Real.log A :=
    Real.log_le_log (by exact_mod_cast hL) (by exact_mod_cast hLA)
  have hLf : L ∈ Icc 1 A := mem_Icc.mpr ⟨hL,hLA⟩
  have hratio : (L:ℝ)/(L.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
    (ratio_totient_le L hL).trans (mul_le_mul_of_nonneg_left (by linarith)
      weightConstant_nonneg)
  have hrewrite :
      (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) =
      ∑ q ∈ Icc 1 A, (∑ d ∈ q.divisors,F d)/(q.totient:ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q hq
    have hq0 : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
    have hmem : L ∈ q.divisors ↔ L ∣ q := by simp [Nat.mem_divisors,hq0]
    by_cases hdiv : L ∣ q
    · have h := hmem.mpr hdiv
      simp [F,hdiv,h]
    · have h : L ∉ q.divisors := fun hm => hdiv (hmem.mp hm)
      simp [F,hdiv,h]
  have hsum : (∑ d ∈ Icc 1 A,F d/(d.totient:ℝ)) = (L:ℝ)/(L.totient:ℝ) := by
    simp [F,ite_div,hLf]
  rw [hrewrite]
  apply (sum_conductor_weights A F hF).trans
  rw [hsum,pow_two]
  exact mul_le_mul_of_nonneg_right hratio (mul_nonneg weightConstant_nonneg (by linarith))

def productCoefficient (q d₁ d₂ D : ℕ) : ℝ :=
  Real.sqrt d₁ * Real.sqrt d₂ * q * (1+Real.log q) /
    ((q.totient:ℝ)^2 * Real.sqrt D)

/-- At most four logarithms are lost when summing the high-product
conductor coefficient over all moduli divisible by both original
conductors. No assumption on gcd(n,q) occurs. -/
theorem productCoefficientFamily (A d₁ d₂ D : ℕ)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hD : 0 < D) :
    (∑ q ∈ (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q),
       productCoefficient q d₁ d₂ D) ≤
      weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  let L := Nat.lcm d₁ d₂
  have hL : 0 < L := Nat.lcm_pos h₁ h₂
  have hset :
      (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q) =
        (Icc 1 A).filter (fun q => L ∣ q) := by
    ext q
    simp [L,Nat.lcm_dvd_iff]
  have hD' : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hD)
  have hd₁ : d₁ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_left d₁ d₂)
  have hd₂ : d₂ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_right d₁ d₂)
  have hroot : Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ) ≤ (L:ℝ) := by
    calc
      _ ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hd₁))
          (Real.sqrt_le_sqrt (by exact_mod_cast hd₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  by_cases hLA : L≤A
  · have hA : 0<A := hL.trans_le hLA
    have hlogA : 0≤Real.log A := Real.log_nonneg (by exact_mod_cast hA)
    let C := weightConstant*(1+Real.log A)^2/Real.sqrt D
    have hC : 0≤C := by
      dsimp [C]
      exact div_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
    have ht (q : ℕ) (hq : q∈(Icc 1 A).filter (fun q => L ∣ q)) :
        productCoefficient q d₁ d₂ D ≤ C*((L:ℝ)/(q.totient:ℝ)) := by
      have hq1 : 0<q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hqA := (mem_Icc.mp (mem_filter.mp hq).1).2
      have hlogq : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have hlog : Real.log q≤Real.log A :=
        Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast hqA)
      have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hr : (q:ℝ)/(q.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
        (ratio_totient_le q hq1).trans
          (mul_le_mul_of_nonneg_left (by linarith) weightConstant_nonneg)
      calc
        _ = (Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ)/(q.totient:ℝ))*
            ((q:ℝ)/(q.totient:ℝ))*(1+Real.log q)/Real.sqrt D := by
          unfold productCoefficient
          ring
        _ ≤ ((L:ℝ)/(q.totient:ℝ))*(weightConstant*(1+Real.log A))*
            (1+Real.log A)/Real.sqrt D := by
          apply div_le_div_of_nonneg_right _ hD'.le
          apply mul_le_mul _ (by linarith) (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg weightConstant_nonneg (by linarith)))
          exact mul_le_mul (div_le_div_of_nonneg_right hroot hφ.le) hr
            (by positivity) (by positivity)
        _ = _ := by dsimp [C]; ring
    rw [hset]
    calc
      _ ≤ ∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), C*((L:ℝ)/(q.totient:ℝ)) :=
        sum_le_sum ht
      _ = C*(∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) :=
        (mul_sum ..).symm
      _ ≤ C*(weightConstant*(1+Real.log A))^2 :=
        mul_le_mul_of_nonneg_left (commonMultipleTotientWeight A L hL hLA) hC
      _ = _ := by dsimp [C]; ring
  · have he : (Icc 1 A).filter (fun q => L ∣ q)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hq' := mem_filter.mp hq
      exact hLA ((Nat.le_of_dvd (mem_Icc.mp hq'.1).1 hq'.2).trans (mem_Icc.mp hq'.1).2)
    rw [hset,he,sum_empty]
    exact div_nonneg (mul_nonneg (pow_nonneg weightConstant_nonneg _) (by positivity)) (Real.sqrt_nonneg _)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorBoundaryEnergy.lean; sha256 fd93dd2c99866510f6f2eeb1d38654034f27945644496fe4bae574e45cf37b09 -/
section
/-!
Uniform energy of a clipped interval, with no prime distribution input.
The centered model term costs only reciprocal totients. This is used
on boundary windows of length at most h rather than on the full bulk.
-/
open Finset BombieriVinogradov.LargeSieve InnerFloorLinearTotient
open GoldbachGRHWindow (additiveModel)
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem additiveIntervalFamilyEnergy (A N : ℕ) (M : ℤ)
    (a : ℤ → ℂ) (hA : 0 < A) (W : ℝ) (hW : 0 ≤ W)
    (ha : ∀ k∈range N, ‖shiftedIntervalCoefficients a M k‖ ≤ W) :
    (∑ q∈Icc 1 A,modulusAdditiveEnergy a M N q) ≤
      64*((N:ℝ)+(A:ℝ)^2)*(N:ℝ)*W^2 := by
  rw [sum_modulusAdditiveEnergy_eq_fareySamples]
  apply (additiveLargeSieve hA (shiftedIntervalCoefficients a M)).trans
  have hs : (∑ k∈range N, ‖shiftedIntervalCoefficients a M k‖^2) ≤
      (N:ℝ)*W^2 := by
    calc
      _ ≤ ∑ _k∈range N,W^2 :=
        sum_le_sum fun k hk => pow_le_pow_left₀ (norm_nonneg _) (ha k hk) 2
      _ = _ := by simp [nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

theorem sum_unitModelEnergy (q : ℕ) [NeZero q] :
    (∑ u : (ZMod q)ˣ, ‖additiveModel q (u:ZMod q)‖^2) ≤
      1/(q.totient:ℝ) := by
  have hφ : 0 < (q.totient:ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hterm (u : (ZMod q)ˣ) : ‖additiveModel q (u:ZMod q)‖ ≤
      1/(q.totient:ℝ) := by
    rw [GoldbachGRHWindow.additiveModel_eq_moebius _ u.isUnit,norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (DyadicMixedB4MoebiusGauss.norm_moebiusComplex_le_one q)
      hφ.le
  calc
    _ ≤ ∑ _u : (ZMod q)ˣ, (1/(q.totient:ℝ))^2 :=
      sum_le_sum fun u _ => pow_le_pow_left₀ (norm_nonneg _) (hterm u) 2
    _ = _ := by
      rw [sum_const,nsmul_eq_mul,card_univ,ZMod.card_units_eq_totient]
      field_simp

def centeredIntervalEnergy (a : ℤ → ℂ) (M : ℤ) (N q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u -
      (N:ℂ)*additiveModel q (u:ZMod q)‖^2

theorem centeredIntervalEnergy_le (a : ℤ → ℂ) (M : ℤ) (N q : ℕ)
    (hq : 0 < q) :
    centeredIntervalEnergy a M N q ≤
      2*modulusAdditiveEnergy a M N q+2*(N:ℝ)^2/(q.totient:ℝ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [modulusAdditiveEnergy_eq]
  simp only [centeredIntervalEnergy,dif_neg hq.ne']
  have hterm (u : (ZMod q)ˣ) :
      ‖intervalAdditiveResidueSum a M N q u -
        (N:ℂ)*additiveModel q (u:ZMod q)‖^2 ≤
        2*‖intervalAdditiveResidueSum a M N q u‖^2+
        2*(N:ℝ)^2*‖additiveModel q (u:ZMod q)‖^2 := by
    have hs := norm_sub_le (intervalAdditiveResidueSum a M N q u)
      ((N:ℂ)*additiveModel q (u:ZMod q))
    rw [norm_mul,Complex.norm_natCast] at hs
    exact (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
      (by
        have H := sq_nonneg (‖intervalAdditiveResidueSum a M N q u‖ -
          (N:ℝ)*‖additiveModel q (u:ZMod q)‖)
        nlinarith only [H])
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, (2*‖intervalAdditiveResidueSum a M N q u‖^2+
        2*(N:ℝ)^2*‖additiveModel q (u:ZMod q)‖^2) := sum_le_sum fun u _ => hterm u
    _ = 2*(∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖^2)+
        2*(N:ℝ)^2*(∑ u : (ZMod q)ˣ, ‖additiveModel q (u:ZMod q)‖^2) := by
      rw [sum_add_distrib,← mul_sum,← mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_unitModelEnergy q)
        (show (0:ℝ) ≤ 2*(N:ℝ)^2 from by positivity)
      calc
        _ ≤ 2*(∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖^2)+
            2*(N:ℝ)^2*(1/(q.totient:ℝ)) := add_le_add le_rfl h
        _ = _ := by
          simp only [div_eq_mul_inv,one_mul]
          congr 1
          congr 1
          apply sum_congr
          · ext u
            simp
          · intro u _
            rfl
          all_goals simp only [one_mul]

/-- For any interval of N terms, the total centered reduced numerator
energy has at most a quadratic logarithmic model cost. -/
theorem centeredIntervalFamilyEnergy (A N : ℕ) (M : ℤ)
    (a : ℤ → ℂ) (hA : 0 < A) (W : ℝ) (hW : 0 ≤ W)
    (ha : ∀ k∈range N, ‖shiftedIntervalCoefficients a M k‖ ≤ W) :
    (∑ q∈Icc 1 A,centeredIntervalEnergy a M N q) ≤
      128*((N:ℝ)+(A:ℝ)^2)*(N:ℝ)*W^2+
      2*(N:ℝ)^2*(weightConstant*(1+Real.log A))^2 := by
  have hr := commonMultipleTotientWeight A 1 (by decide) hA
  simp only [one_dvd,filter_true,Nat.cast_one] at hr
  calc
    _ ≤ ∑ q∈Icc 1 A, (2*modulusAdditiveEnergy a M N q+2*(N:ℝ)^2/(q.totient:ℝ)) :=
      sum_le_sum fun q hq => centeredIntervalEnergy_le a M N q (mem_Icc.mp hq).1
    _ = 2*(∑ q∈Icc 1 A,modulusAdditiveEnergy a M N q)+
      2*(N:ℝ)^2*(∑ q∈Icc 1 A,1/(q.totient:ℝ)) := by
      rw [sum_add_distrib,← mul_sum]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left
        (additiveIntervalFamilyEnergy A N M a hA W hW ha) (by norm_num : (0:ℝ)≤2)
      have h2 := mul_le_mul_of_nonneg_left hr (by positivity : 0≤2*(N:ℝ)^2)
      linarith only [h1,h2]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGeometry.lean; sha256 98b89eceb61c72064eefbe955b847da8b66c3d6c5995347341a1f2977e28a2d2 -/
section
/- Geometry reduction only; this file does not claim the published asymptotic estimate. -/
namespace InnerFloorResearch

def arcSet (B : ℕ) (r n : ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ r / ((q : ℝ) * n)}

theorem arcSet_mono {B C : ℕ} {r s n : ℝ}
    (hB : B ≤ C) (hr : r ≤ s) (hn : 0 ≤ n) :
    arcSet B r n ⊆ arcSet C s n := by
  intro t ht
  obtain ⟨q,a,hq,hqb,ha,hcop,hclose⟩ := ht
  exact ⟨q,a,hq,hqb.trans hB,ha,hcop,hclose.trans
    (div_le_div_of_nonneg_right hr (mul_nonneg (Nat.cast_nonneg q) hn))⟩

theorem inner_remainder_eq (Q B : ℕ) (r R u n : ℝ)
    (hr : r ≤ R) (hu : u ≤ R) (hn : 0 ≤ n) :
    (((arcSet B R n \ arcSet Q r n) \
      (arcSet Q R n \ arcSet Q r n)) ∩ arcSet B u n) =
      arcSet B u n \ arcSet Q R n := by
  have hA := arcSet_mono (B := Q) (C := Q) (r := r) (s := R) le_rfl hr hn
  have hI := arcSet_mono (B := B) (C := B) (r := u) (s := R) le_rfl hu hn
  ext t
  constructor
  · rintro ⟨⟨⟨hw,ha⟩,hl⟩,hi⟩
    exact ⟨hi,fun h => hl ⟨h,ha⟩⟩
  · rintro ⟨hi,hl⟩
    have ha : t ∉ arcSet Q r n := fun h => hl (hA h)
    exact ⟨⟨⟨hI hi,ha⟩,fun h => hl h.1⟩,hi⟩

theorem medium_witness (Q B : ℕ) (u R n : ℝ)
    (hu : u ≤ R) (hn : 0 ≤ n) {t : ℝ}
    (ht : t ∈ arcSet B u n \ arcSet Q R n) :
    ∃ q a : ℕ, Q < q ∧ 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ u / ((q : ℝ) * n) := by
  obtain ⟨hi,hl⟩ := ht
  obtain ⟨q,a,hq,hqb,ha,hcop,hclose⟩ := hi
  have hlarge : Q < q := by
    by_contra! hsmall
    apply hl
    exact ⟨q,a,hq,hsmall,ha,hcop,hclose.trans
      (div_le_div_of_nonneg_right hu (mul_nonneg (Nat.cast_nonneg q) hn))⟩
  exact ⟨q,a,hlarge,hq,hqb,ha,hcop,hclose⟩


/-- Separation for two reduced rational windows with independently specified widths.
The cross-multiplication argument adapts MajorNumeratorDilation's
cross_eq_of_overlap (Apache-2.0; original separation credited to wzhxzkk, PR 153). -/
theorem overlap_center_eq {q r a b : ℕ} {u v n t : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hn : 0 < n)
    (hc : a.Coprime q) (hd : b.Coprime r)
    (hsmall : u*(r:ℝ)+v*(q:ℝ)<n)
    (ha : |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n))
    (hb : |t-(b:ℝ)/r| ≤ v/((r:ℝ)*n)) :
    q=r ∧ a=b := by
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hprod : 0 < (q:ℝ)*r := mul_pos hqr hrr
  have hrad : u/((q:ℝ)*n)+v/((r:ℝ)*n)<1/((q:ℝ)*r) := by
    calc
      _ = (u*(r:ℝ)+v*(q:ℝ))/((q:ℝ)*r*n) := by
        field_simp
      _ < n/((q:ℝ)*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).2 hsmall
      _ = _ := by field_simp
  have he : a*r=b*q := by
    by_contra hne
    have hsep : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp,
        abs_div, abs_of_pos hprod]
      apply (div_le_div_iff_of_pos_right hprod).2
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r-b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r-b*q)]
    have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at ht
    linarith
  have hdiv1 : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv2 : r ∣ q := hd.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv1 hdiv2
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

def mediumBand (Q B : ℕ) (u n : ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, Q<q ∧ 1≤q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n)}

/-- The excluded low-modulus mask can be dropped exactly once the rational
separation inequality holds. This statement makes no estimate of prime sums. -/
theorem masked_medium_eq (Q B : ℕ) (u R n : ℝ)
    (hu : 0≤u) (huR : u≤R) (hn : 0<n)
    (hsmall : u*(Q:ℝ)+R*(B:ℝ)<n) :
    arcSet B u n \ arcSet Q R n = mediumBand Q B u n := by
  ext t
  constructor
  · exact fun ht => medium_witness Q B u R n huR hn.le ht
  · rintro ⟨q,a,hqQ,hq,hqB,ha,hcop,hclose⟩
    refine ⟨⟨q,a,hq,hqB,ha,hcop,hclose⟩,?_⟩
    rintro ⟨r,b,hr,hrQ,hb,hd,hnear⟩
    have hsmall' : u*(r:ℝ)+R*(q:ℝ)<n :=
      (add_le_add
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hrQ) hu)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hqB) (hu.trans huR))).trans_lt hsmall
    have he := overlap_center_eq (by omega : 0<q) (by omega : 0<r)
      hn hcop hd hsmall' hclose hnear
    omega

theorem mediumBand_unique (Q B : ℕ) (u n : ℝ) (hu : 0≤u) (hn : 0<n)
    (hsmall : 2*u*(B:ℝ)<n)
    {q r a b : ℕ} {t : ℝ}
    (hq : Q<q) (hr : Q<r) (hqB : q≤B) (hrB : r≤B)
    (hc : a.Coprime q) (hd : b.Coprime r)
    (ha : |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n))
    (hb : |t-(b:ℝ)/r| ≤ u/((r:ℝ)*n)) :
    q=r ∧ a=b := by
  apply overlap_center_eq (by omega : 0<q) (by omega : 0<r) hn hc hd _ ha hb
  have h1 := mul_le_mul_of_nonneg_left (show (q:ℝ)≤B by exact_mod_cast hqB) hu
  have h2 := mul_le_mul_of_nonneg_left (show (r:ℝ)≤B by exact_mod_cast hrB) hu
  linarith

end InnerFloorResearch

end

/-! BEGIN InnerFloorModelTransfer.lean; sha256 d527e1221bbcc5f08a101c5dde1dd1d5616138c7b5d2d6997f32c38c9ebae91a -/
section
open Finset MeasureTheory Filter
open scoped Interval Topology Classical

namespace InnerFloorResearch

noncomputable section
set_option maxHeartbeats 1500000

open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHArcs (center centers mem_centers)
open GoldbachGRHApproximation (integrand)
open GoldbachGRHModel (model model_continuous)

def realRadius (n : ℕ) (u : ℝ) (q : ℕ) : ℝ := u / ((q : ℝ) * (n : ℝ))

def realArc (n : ℕ) (u : ℝ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ realRadius n u i.1}

theorem realArc_eq_Icc (n : ℕ) (u : ℝ) (i : ℕ × ℕ) :
    realArc n u i =
      Set.Icc (center i - realRadius n u i.1) (center i + realRadius n u i.1) := by
  ext t
  change |t - center i| ≤ _ ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

def mediumIndices (Q A : ℕ) : Finset (ℕ × ℕ) :=
  (centers A).filter (fun i => Q < i.1)

theorem mediumIndices_spec {Q A : ℕ} {i : ℕ × ℕ} :
    i ∈ mediumIndices Q A ↔ Q < i.1 ∧ i.1 ≤ A ∧ i.2 ≤ i.1 ∧ i.2.Coprime i.1 := by
  simp only [mediumIndices, mem_filter, mem_centers]
  constructor
  · rintro ⟨⟨_, hA, ha, hc⟩, hQ⟩
    exact ⟨hQ, hA, ha, hc⟩
  · rintro ⟨hQ, hA, ha, hc⟩
    exact ⟨⟨by omega, hA, ha, hc⟩, hQ⟩

theorem mediumBand_eq_union (n Q A : ℕ) (u : ℝ) :
    mediumBand Q A u n = ⋃ i ∈ mediumIndices Q A, realArc n u i := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨q,a,hQ,_,hA,ha,hc,ht⟩
    exact ⟨(q,a), mediumIndices_spec.mpr ⟨hQ,hA,ha,hc⟩, ht⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨hQ,hA,ha,hc⟩ := mediumIndices_spec.mp hi
    exact ⟨q,a,hQ,by omega,hA,ha,hc,ht⟩

theorem measurable_mediumBand (n Q A : ℕ) (u : ℝ) :
    MeasurableSet (mediumBand Q A u n) := by
  rw [mediumBand_eq_union]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => by
    rw [realArc_eq_Icc]
    exact measurableSet_Icc

def arcCell (n : ℕ) (u : ℝ) (i : ℕ × ℕ) : Set ℝ := realArc n u i ∩ Set.Ioc 0 1

theorem measurable_arcCell (n : ℕ) (u : ℝ) (i : ℕ × ℕ) :
    MeasurableSet (arcCell n u i) := by
  unfold arcCell
  rw [realArc_eq_Icc]
  exact measurableSet_Icc.inter measurableSet_Ioc

theorem arcCells_disjoint {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) :
    (↑(mediumIndices Q A) : Set (ℕ × ℕ)).PairwiseDisjoint (arcCell n u) := by
  rintro ⟨q,a⟩ hi ⟨r,b⟩ hj hij
  change Disjoint (arcCell n u (q,a)) (arcCell n u (r,b))
  rw [Set.disjoint_left]
  intro t ht ht'
  obtain ⟨hq,hqA,_,hc⟩ := mediumIndices_spec.mp (show (q,a) ∈ mediumIndices Q A from hi)
  obtain ⟨hr,hrA,_,hd⟩ := mediumIndices_spec.mp (show (r,b) ∈ mediumIndices Q A from hj)
  obtain ⟨hqr,hab⟩ := mediumBand_unique Q A u (n : ℝ) hu (by exact_mod_cast hn)
    hsep hq hr hqA hrA hc hd ht.1 ht'.1
  exact hij (Prod.ext hqr hab)

/-- Interior centers yield the full symmetric beta-window. The singleton
at zero does not contribute to the integral. -/
theorem arcCell_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n q a : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u) (hun : u ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hc : a.Coprime q) (G : ℝ → E) :
    (∫ t in arcCell n u (q,a), G (t - center (q,a))) =
      ∫ t in -(realRadius n u q)..(realRadius n u q), G t := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha0 : 1 ≤ a := by
    by_contra! h
    have he : a = 0 := by omega
    have h1 := (Nat.coprime_zero_left q).mp (he ▸ hc)
    omega
  have haq : a + 1 ≤ q := by
    by_contra! h
    have he : a = q := by omega
    have h1 : q = 1 := by simpa [he, Nat.Coprime] using hc
    omega
  have hrad : 0 ≤ realRadius n u q := div_nonneg hu (mul_pos hqR hnR).le
  have hr : realRadius n u q ≤ 1/(q : ℝ) := by
    apply (div_le_iff₀ (mul_pos hqR hnR)).2
    convert hun using 1
    field_simp
  have hleft : realRadius n u q ≤ center (q,a) :=
    hr.trans (div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le)
  have hright : center (q,a) + realRadius n u q ≤ 1 := by
    apply (add_le_add_right hr _).trans
    change (a : ℝ)/q + 1/(q : ℝ) ≤ 1
    rw [← add_div, div_le_one hqR]
    exact_mod_cast haq
  have hsub : realArc n u (q,a) ⊆ Set.Icc 0 1 := by
    rw [realArc_eq_Icc]
    exact Set.Icc_subset_Icc (sub_nonneg.mpr hleft) hright
  have he : arcCell n u (q,a) =ᵐ[volume] realArc n u (q,a) := by
    have h : Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
    filter_upwards [h] with t ht
    change (t ∈ realArc n u (q,a) ∧ t ∈ Set.Ioc 0 1) ↔ t ∈ realArc n u (q,a)
    exact ⟨And.left, fun hp => ⟨hp, ht.mpr (hsub hp)⟩⟩
  have hInt :
      (∫ t in arcCell n u (q,a), G (t - center (q,a))) =
        ∫ t in realArc n u (q,a), G (t - center (q,a)) :=
    setIntegral_congr_set he
  rw [hInt,
    realArc_eq_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hrad] :
      center (q,a) - realRadius n u q ≤ center (q,a) + realRadius n u q),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

theorem sum_mediumIndices {E : Type*} [AddCommMonoid E] (Q A : ℕ)
    (F : ℕ × ℕ → E) :
    (∑ i ∈ mediumIndices Q A, F i) =
      ∑ q ∈ Ioc Q A, ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), F (q,a) := by
  have he : (Icc 1 A).filter (fun q => Q < q) = Ioc Q A := by
    ext q
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [mediumIndices, sum_filter, GoldbachGRHArcs.sum_centers_eq, ← he]
  conv_rhs => rw [sum_filter]
  apply sum_congr rfl
  intro q hq
  by_cases h : Q < q <;> simp [h]

def mediumIntegral (n Q A : ℕ) (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (mediumBand Q A u n).indicator (integrand n) t

def mediumModel (n Q A : ℕ) (u : ℝ) : ℂ :=
  ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, model n i t ^ 2 * phase (-(n : ℝ)*t)

def mediumCellEnergy (n Q A : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, ‖primeSum n t - model n i t‖^2

theorem mediumIntegral_eq_sum {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) :
    mediumIntegral n Q A u = ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, integrand n t := by
  have hf : Continuous (integrand n) := by unfold integrand primeSum phase; fun_prop
  have hUnion :
      (⋃ i ∈ mediumIndices Q A, arcCell n u i) =
        mediumBand Q A u n ∩ Set.Ioc 0 1 := by
    ext t
    rw [mediumBand_eq_union]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, arcCell]
    constructor
    · rintro ⟨i, hi, ha, ht⟩
      exact ⟨⟨i,hi,ha⟩,ht⟩
    · rintro ⟨⟨i,hi,ha⟩,ht⟩
      exact ⟨i,hi,ha,ht⟩
  rw [mediumIntegral, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator (measurable_mediumBand n Q A u), Set.inter_comm (Set.Ioc 0 1) (mediumBand Q A u n), ← hUnion]
  exact integral_biUnion_finset (mediumIndices Q A) (fun i _ => measurable_arcCell n u i)
    (arcCells_disjoint hn hu hsep) (fun i _ => (hf.intervalIntegrable 0 1).1.mono_set
      Set.inter_subset_right)

theorem mediumModel_re {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hQ : 1 ≤ Q)
    (hu : 0 ≤ u) (hun : u ≤ (n : ℝ)) :
    (mediumModel n Q A u).re =
      ∑ q ∈ Ioc Q A, (GoldbachExplicitModeledMajor.coefficient q n).re *
        GoldbachGRHKernel.mass n (realRadius n u q) := by
  have he :
      mediumModel n Q A u =
        ∑ q ∈ Ioc Q A, GoldbachExplicitModeledMajor.coefficient q n *
          (GoldbachGRHKernel.mass n (realRadius n u q) : ℂ) := by
    rw [mediumModel, sum_mediumIndices]
    apply sum_congr rfl
    intro q hq
    have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
    have hR : ((range (q+1)).filter (fun a => a.Coprime q)) =
        (range q).filter (fun a => a.Coprime q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨ha,hc⟩
        have hne : a ≠ q := by
          intro heq
          have h1 : q = 1 := by simpa [heq,Nat.Coprime] using hc
          omega
        exact ⟨by omega,hc⟩
      · rintro ⟨ha,hc⟩
        exact ⟨by omega,hc⟩
    rw [hR, ← GoldbachGRHModelAssembly.sum_signedFactor, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨haq,hcop⟩ := mem_filter.mp ha
    simp_rw [GoldbachGRHModelAssembly.model_square_eq]
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal,
      arcCell_translate hn hu hun hq₂ (mem_range.mp haq).le hcop
        (fun t : ℝ => ‖GoldbachGRHKernel.kernel n t‖^2)] <;> rfl
  rw [he]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- The Ramanujan model has the required signed lower floor at arbitrary
real widths up to half the ambient length. The weights are kernel masses
on nested beta-intervals, so the prefix bound is used by summation by parts. -/
theorem realWidthModelFloor (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n Q A : ℕ, 0 < n → Even n → 1 ≤ Q → K ≤ Q → Q ≤ A →
      ∀ u : ℝ, 0 < u → 2*u ≤ (n : ℝ) →
        -(ε*(n : ℝ)) ≤ (mediumModel n Q A u).re := by
  obtain ⟨K,hK⟩ := GoldbachGRHSignedModel.harmonic_suffix_floor (ε/2) (by positivity)
  refine ⟨K, ?_⟩
  intro n Q A hn he hQ hstart hQA u hu hun
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let w (q : ℕ) := GoldbachGRHKernel.mass n (realRadius n u q)
  have hpos (q : ℕ) (hq : Q ≤ q) : 0 < realRadius n u q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hQ.trans hq
    unfold realRadius
    exact div_pos hu (mul_pos (by linarith) hnR)
  have hmono (q : ℕ) (hq : Q ≤ q) : w (q+1) ≤ w q := by
    apply GoldbachGRHKernel.mass_mono n (hpos (q+1) (by omega)).le
    have hqR : (0 : ℝ) < q := by exact_mod_cast hQ.trans hq
    unfold realRadius
    exact div_le_div_of_nonneg_left hu.le (mul_pos hqR hnR) (by
      push_cast
      nlinarith only [hnR])
  have hw (q : ℕ) (hq : Q ≤ q) : 0 ≤ w q :=
    GoldbachGRHKernel.mass_nonneg n (hpos q hq).le
  have hr : realRadius n u Q ≤ 1/2 := by
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    apply (div_le_iff₀ (by positivity : 0 < (Q : ℝ)*(n : ℝ))).2
    nlinarith only [hun, mul_le_mul_of_nonneg_right hQR hnR.le]
  have hwQ : w Q ≤ (n : ℝ)+1 :=
    sub_nonneg.mp (GoldbachGRHKernel.mass_loss n (hpos Q le_rfl) hr).1
  have hweight := BandTail.weighted_prefix_lower Q A
    (fun q => (GoldbachExplicitModeledMajor.coefficient q n).re) w
    (ε/2) hQA (by positivity) hw hmono (by
      intro i hi _
      have hh := hK Q hstart n i he hi
      refine hh.trans (le_of_eq (sum_congr rfl ?_))
      intro q hq
      exact (GoldbachGRHSignedModel.coefficient_re_eq n q
        ((Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1)).symm)
  rw [mediumModel_re hn hQ hu.le (by linarith)]
  change -(ε*(n : ℝ)) ≤ ∑ q ∈ Ioc Q A, _ * w q
  apply le_trans _ hweight
  apply neg_le_neg
  calc
    _ ≤ (ε/2)*((n : ℝ)+1) := mul_le_mul_of_nonneg_left hwQ (by positivity)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hn1 hε.le]

/-- The finite Fourier reduction with real width and the exact denominator
band. The modulus factor is in `GBSkirtVariance.mass`. -/
theorem middleEnergy_of_window {n Q A h : ℕ} {u : ℝ} (hn : 0 < n)
    (hQ : 1 ≤ Q) (hh : 0 < h) (hu : 0 ≤ u) (hun : u ≤ n)
    (hwidth : 6*(h : ℝ)*u ≤ n) :
    (h : ℝ)^2 * mediumCellEnergy n Q A u ≤
      8 * ∑ q ∈ Ioc Q A, GBSkirtVariance.mass q n h := by
  rw [mediumCellEnergy, sum_mediumIndices]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply sum_le_sum
  intro q hq
  have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
  have hq0 : 0 < q := by omega
  letI : NeZero q := ⟨hq0.ne'⟩
  let δ := realRadius n u q
  let E (a : ZMod q) : ℝ := ∫ β in -δ..δ,
    ‖GoldbachWindow.poly (n+1) (GoldbachGRHAnalytic.errorCoeff a) β‖^2
  have hd : 0 ≤ δ := by unfold δ realRadius; positivity
  have hw : 6*(h : ℝ)*δ ≤ 1 := by
    have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq0
    unfold δ realRadius
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (q : ℝ)*(n : ℝ)), one_mul]
    exact hwidth.trans (by nlinarith only [mul_le_mul_of_nonneg_left hqR (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hE (a : ZMod q) : 0 ≤ E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hc (a : ℕ) (ha : a ∈ (range (q+1)).filter (fun a => a.Coprime q)) :
      (∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) = E (a : ZMod q) := by
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    have hUnit := (ZMod.isUnit_iff_coprime a q).2 hcop
    let G (β : ℝ) := ‖GoldbachWindow.poly (n+1)
      (GoldbachGRHAnalytic.errorCoeff (a : ZMod q)) β‖^2
    have he (t : ℝ) : G (t - center (q,a)) = ‖primeSum n t - model n (q,a) t‖^2 := by
      unfold G
      rw [GoldbachGRHAnalytic.shifted_error_eq, GoldbachGRHWindow.additiveModel_eq_moebius _ hUnit]
      unfold model
      rw [show (a : ℝ)/q+(t-center (q,a)) = t by unfold center; ring]
    calc
      _ = ∫ t in arcCell n u (q,a), G (t - center (q,a)) := by simp_rw [he]
      _ = E (a : ZMod q) :=
        arcCell_translate hn hu hun hq₂ (Nat.lt_succ_iff.mp (mem_range.mp haq)) hcop G
  have hcells :
      (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
        ∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) ≤
        2 * ∑ a : ZMod q, E a :=
    (le_of_eq (sum_congr rfl hc)).trans (GoldbachGRHArcs.sum_numerators_le_real q E hE)
  have hden := GBSkirtVariance.denominator_bound (q := q) n h δ hh hd hw
  change (h : ℝ)^2/4 * (∑ a : ZMod q, E a) ≤ _ at hden
  rw [GBSkirtVariance.mass, dite_eq_right hq0.ne']
  linarith only [mul_le_mul_of_nonneg_left hcells (sq_nonneg (h : ℝ)), hden]

theorem signedMediumDifference {n Q A : ℕ} {u η : ℝ} (hn : 2 ≤ n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) (hη : 0 < η) :
    ‖mediumIntegral n Q A u - mediumModel n Q A u‖ ≤
      (1+1/η)*mediumCellEnergy n Q A u + η*((n : ℝ)+1)*(Real.log (n : ℝ))^2 := by
  let osc (t : ℝ) := phase (-(n : ℝ)*t)
  have hosc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  rw [mediumIntegral_eq_sum (by omega) hu hsep, mediumModel, ← sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in arcCell n u i, integrand n t) -
        (∫ t in arcCell n u i, model n i t ^ 2 * osc t) =
      ∫ t in arcCell n u i, (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : arcCell n u i ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_right
    have h₁ : IntegrableOn (integrand n) (arcCell n u i) volume :=
      (((hS.pow 2).mul hosc).intervalIntegrable 0 1).1.mono_set hpart
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t) (arcCell n u i) volume :=
      ((((model_continuous n i).pow 2).mul hosc).intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [integrand, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  have hb := GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le
    (mediumIndices Q A) (arcCell n u) (fun i _ => measurable_arcCell n u i)
    (fun _ _ => Set.inter_subset_right) (arcCells_disjoint (by omega) hu hsep)
    (primeSum n) (model n) osc hS (fun i _ => model_continuous n i) hosc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n : ℝ)*t)))) hη
  exact hb.trans (by
    unfold mediumCellEnergy
    rw [mul_assoc η]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le) _)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorReducedModelTransfer.lean; sha256 074751e694b8e3e4dbf7fabbefb9eaa6db74dff7a0b8bd53a410e0b27cf1fc6e -/
section
/-!
Exact reduced-numerator bridge for real-width model error. Allows an
independent window for each denominator band: 6 h u <= Q n.
The unit/numerator bijection is adapted from accepted
ShortProgressionsMeanTheta (XBribo #3789, pinned upstream 1fe24b28).
No analytic input is assumed beyond the already verified Gallagher
inequality. This replaces the earlier all-residue variance bound.
-/
open Finset MeasureTheory
open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHArcs (center)
open GoldbachGRHModel (model)
open scoped Classical Interval
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem inner_sum_units_eq_sum_coprime (q : ℕ) [NeZero q]
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ a : (ZMod q)ˣ, f ((a : ZMod q).val)) =
      ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f a := by
  refine Finset.sum_bij (fun (a : (ZMod q)ˣ) _ => (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ hab
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (a : ZMod q), ← ZMod.natCast_zmod_val (b : ZMod q), hab]
  · intro a ha
    obtain ⟨haq, hac⟩ := Finset.mem_filter.mp ha
    have hu := (ZMod.isUnit_iff_coprime a q).mpr hac
    exact ⟨hu.unit, Finset.mem_univ _, by
      rw [hu.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp haq)]⟩
  · intro a _
    rfl

theorem middleEnergy_of_reducedWindow {n Q A h : ℕ} {u : ℝ} (hn : 0 < n)
    (hQ : 1 ≤ Q) (hh : 0 < h) (hu : 0 ≤ u) (hun : u ≤ n)
    (hwidth : 6*(h : ℝ)*u ≤ (Q:ℝ)*n) :
    (h : ℝ)^2 * mediumCellEnergy n Q A u ≤
      4 * ∑ q ∈ Ioc Q A, ∑ m∈range (n+1+h), reducedMovingLevelEnergy q n h m := by
  rw [mediumCellEnergy, sum_mediumIndices]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply sum_le_sum
  intro q hq
  have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
  have hq0 : 0 < q := by omega
  letI : NeZero q := ⟨hq0.ne'⟩
  let δ := realRadius n u q
  let E (a : ZMod q) : ℝ := ∫ β in -δ..δ,
    ‖GoldbachWindow.poly (n+1) (GoldbachGRHAnalytic.errorCoeff a) β‖^2
  have hd : 0 ≤ δ := by unfold δ realRadius; positivity
  have hw : 6*(h : ℝ)*δ ≤ 1 := by
    have hqR : (Q:ℝ) ≤ q := by exact_mod_cast (mem_Ioc.mp hq).1.le
    unfold δ realRadius
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (q : ℝ)*(n : ℝ)), one_mul]
    exact hwidth.trans (mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg n))
  have hE (a : ZMod q) : 0 ≤ E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hc (a : ℕ) (ha : a ∈ (range (q+1)).filter (fun a => a.Coprime q)) :
      (∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) = E (a : ZMod q) := by
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    have hUnit := (ZMod.isUnit_iff_coprime a q).2 hcop
    let G (β : ℝ) := ‖GoldbachWindow.poly (n+1)
      (GoldbachGRHAnalytic.errorCoeff (a : ZMod q)) β‖^2
    have he (t : ℝ) : G (t - center (q,a)) = ‖primeSum n t - model n (q,a) t‖^2 := by
      unfold G
      rw [GoldbachGRHAnalytic.shifted_error_eq, GoldbachGRHWindow.additiveModel_eq_moebius _ hUnit]
      unfold model
      rw [show (a : ℝ)/q+(t-center (q,a)) = t by unfold center; ring]
    calc
      _ = ∫ t in arcCell n u (q,a), G (t - center (q,a)) := by simp_rw [he]
      _ = E (a : ZMod q) :=
        arcCell_translate hn hu hun hq₂ (Nat.lt_succ_iff.mp (mem_range.mp haq)) hcop G
  have hR : (range (q+1)).filter (fun a => a.Coprime q) =
      (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      refine ⟨?_,hc⟩
      by_contra! h
      have he : a=q := by omega
      subst a
      simp only [Nat.coprime_self] at hc
      omega
    · rintro ⟨ha,hc⟩
      exact ⟨by omega,hc⟩
  have hcells :
      (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
        ∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) =
        ∑ a : (ZMod q)ˣ, E (a:ZMod q) := by
    rw [sum_congr rfl hc,hR,← inner_sum_units_eq_sum_coprime q
      (fun a : ℕ => E (a:ZMod q))]
    simp only [ZMod.natCast_zmod_val]
  rw [hcells]
  have hden := reducedDenominatorBound (q := q) n h δ hh hd hw
  change (h:ℝ)^2/4*(∑ a : (ZMod q)ˣ,E (a:ZMod q)) ≤ _ at hden
  have he (m:ℕ) : reducedMovingLevelEnergy q n h m =
      ∑ a : (ZMod q)ˣ, ‖GoldbachWindow.moving (n+1) h
        (GoldbachGRHAnalytic.errorCoeff (a:ZMod q)) m‖^2 := by
    simp only [reducedMovingLevelEnergy,dif_neg hq0.ne']
  simp_rw [he]
  linarith only [hden]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorClippedMoving.lean; sha256 5a8449680d0cf11c927d178b811922b7cf5a99c5f50d4b362d6d55231a2785d9 -/
section
/-! Exact clipped windows and boundary energy. No zero-free assumption. -/
open Finset BombieriVinogradov.LargeSieve InnerFloorLinearTotient
open GoldbachGRHWindow (primeLog additiveModel)
open GoldbachWindow (moving)
open GoldbachGRHAnalytic (errorCoeff)
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def clipStart (h m : ℕ) : ℕ := m+1-h
def clipEnd (n m : ℕ) : ℕ := min m n
def clipLength (n h m : ℕ) : ℕ := clipEnd n m+1-clipStart h m
def clipShift (h m : ℕ) : ℤ := (clipStart h m:ℤ)-1

theorem clipLength_le (n h m : ℕ) : clipLength n h m ≤ h := by
  unfold clipLength clipStart clipEnd
  omega

theorem clipWindow_card (n h m : ℕ) :
    (GBSkirtVariance.window n h m).card = clipLength n h m := by
  rw [GBSkirtVariance.window,Nat.card_Icc]
  unfold clipLength clipStart clipEnd
  omega

theorem clipNatIntSum (n h m : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) :
    (∑ k∈GBSkirtVariance.window n h m, f (k:ℤ)) =
      ∑ k∈Ioc (clipShift h m) (clipShift h m+(clipLength n h m:ℤ)),f k := by
  apply sum_bij (fun (k : ℕ) _ => (k : ℤ))
  · intro k hk
    simp only [GBSkirtVariance.window,mem_Icc] at hk
    simp only [mem_Ioc,clipShift,clipLength,clipStart,clipEnd]
    omega
  · intro a ha b hb he
    exact_mod_cast he
  · intro k hk
    simp only [mem_Ioc,clipShift,clipLength,clipStart,clipEnd] at hk
    have hk0 : 0 ≤ k := by omega
    refine ⟨k.toNat,?_,Int.toNat_of_nonneg hk0⟩
    simp only [GBSkirtVariance.window,mem_Icc]
    omega
  · intro k hk
    rfl

theorem moving_eq_centeredInterval (n h m : ℕ) {q : ℕ} [NeZero q]
    (a : (ZMod q)ˣ) :
    moving (n+1) h (errorCoeff (a:ZMod q)) m =
      intervalAdditiveResidueSum (fun k : ℤ => primeLog k.toNat)
        (clipShift h m) (clipLength n h m) q a -
      (clipLength n h m:ℂ)*additiveModel q (a:ZMod q) := by
  rw [GoldbachWindow.moving_eq_sum]
  have hI : (range (n+1)).filter (fun k => m+1-h ≤ k ∧ k ≤ m) =
      GBSkirtVariance.window n h m := by
    ext k
    simp only [mem_filter,mem_range,GBSkirtVariance.window,mem_Icc,le_min_iff]
    omega
  rw [hI]
  unfold errorCoeff
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,clipWindow_card]
  congr 1
  unfold intervalAdditiveResidueSum
  rw [← clipNatIntSum n h m
    (fun k : ℤ => primeLog k.toNat * ZMod.stdAddChar ((k:ZMod q)*(a:ZMod q)))]
  apply sum_congr rfl
  intro k _
  simp only [Int.toNat_natCast,Int.cast_natCast]
  rw [mul_comm (a:ZMod q) (k:ZMod q)]

theorem reducedMoving_eq_centeredIntervalEnergy (n h m q : ℕ) :
    reducedMovingLevelEnergy q n h m =
      centeredIntervalEnergy (fun k : ℤ => primeLog k.toNat)
        (clipShift h m) (clipLength n h m) q := by
  by_cases hq : q=0
  · simp [reducedMovingLevelEnergy,centeredIntervalEnergy,hq]
  · letI : NeZero q := ⟨hq⟩
    simp only [reducedMovingLevelEnergy,centeredIntervalEnergy,dif_neg hq]
    exact sum_congr rfl fun a _ => by rw [moving_eq_centeredInterval n h m a]

theorem clipShiftedCoefficient_le (n h m k : ℕ)
    (hk : k∈range (clipLength n h m)) :
    ‖shiftedIntervalCoefficients (fun z : ℤ => primeLog z.toNat)
      (clipShift h m) k‖ ≤ Real.log ((n+2:ℕ):ℝ) := by
  let z := (clipShift h m+(k:ℤ)+1).toNat
  have hz : z≤n := by
    have hk' := mem_range.mp hk
    unfold z clipLength clipShift clipStart clipEnd at *
    omega
  change ‖primeLog z‖ ≤ _
  unfold primeLog
  split_ifs with hp
  · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show z≤n+2 by omega))
  · simp only [Complex.ofReal_zero,norm_zero]
    exact Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega))

def boundaryWindowBudget (A n h : ℕ) : ℝ :=
  128*((h:ℝ)+(A:ℝ)^2)*(h:ℝ)*(Real.log ((n+2:ℕ):ℝ))^2+
    2*(h:ℝ)^2*(weightConstant*(1+Real.log A))^2

/-- Uniform per-window energy for the actual clipped error coefficients. -/
theorem actualClippedWindowFamilyEnergy (A n h m : ℕ) (hA : 0 < A) :
    (∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m) ≤
      boundaryWindowBudget A n h := by
  simp_rw [reducedMoving_eq_centeredIntervalEnergy]
  apply (centeredIntervalFamilyEnergy A (clipLength n h m) (clipShift h m)
    (fun z : ℤ => primeLog z.toNat) hA (Real.log ((n+2:ℕ):ℝ))
    (Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega)))
    (fun k hk => clipShiftedCoefficient_le n h m k hk)).trans
  unfold boundaryWindowBudget
  have hl : (clipLength n h m:ℝ) ≤ h := by exact_mod_cast clipLength_le n h m
  gcongr
  all_goals positivity

theorem reducedMovingLevelEnergy_nonneg (q n h m : ℕ) :
    0 ≤ reducedMovingLevelEnergy q n h m := by
  unfold reducedMovingLevelEnergy
  split_ifs <;> first | exact le_rfl | exact sum_nonneg fun _ _ => sq_nonneg _

/-- Decompose the actual moving family into a bulk primitive window
sum and the at most X+2h endpoint/startup windows. -/
theorem reducedMovingBulkBoundary (A n h X : ℕ)
    (hA : 0 < A) (hAX : A≤X) (hX : X+h≤n) :
    (∑ m∈range (n+1+h), ∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m) ≤
      (weightConstant*(1+Real.log A))^2 *
        (∑ y∈Ico X (n+1-h), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) +
      ((X+2*h:ℕ):ℝ)*boundaryWindowBudget A n h := by
  let S := range (n+1+h)
  let G := Icc (X+h) n
  let E (m : ℕ) := ∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m
  have hGS : G⊆S := by
    intro m hm
    simp only [G,mem_Icc] at hm
    simp only [S,mem_range]
    omega
  have hcard : (S\G).card = X+2*h := by
    rw [card_sdiff_of_subset hGS]
    simp only [S,G,card_range,Nat.card_Icc]
    omega
  have hbulk :
      (∑ m∈G,E m) ≤ (weightConstant*(1+Real.log A))^2 *
        (∑ y∈Ico X (n+1-h), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) := by
    rw [mul_sum]
    have hre : (∑ m∈G,E m) =
        ∑ y∈Ico X (n+1-h), E (y+h) := by
      apply sum_bij (fun m _ => m-h)
      · intro m hm
        simp only [G,mem_Icc] at hm
        simp only [mem_Ico]
        omega
      · intro m hm k hk he
        simp only [G,mem_Icc] at hm hk
        omega
      · intro y hy
        simp only [mem_Ico] at hy
        refine ⟨y+h,?_,by omega⟩
        simp only [G,mem_Icc]
        omega
      · intro m hm
        simp only [G,mem_Icc] at hm
        rw [Nat.sub_add_cancel (by omega : h ≤ m)]
    rw [hre]
    apply sum_le_sum
    intro y hy
    have hy' := mem_Ico.mp hy
    exact interiorReducedMovingFamilyEnergy A n y h (hAX.trans hy'.1) (by omega)
  have hedge : (∑ m∈S\G,E m) ≤ ((X+2*h:ℕ):ℝ)*boundaryWindowBudget A n h := by
    calc
      _ ≤ ∑ _m∈S\G,boundaryWindowBudget A n h :=
        sum_le_sum fun m _ => actualClippedWindowFamilyEnergy A n h m hA
      _ = _ := by rw [sum_const,nsmul_eq_mul,hcard]
  change (∑ m∈S,E m) ≤ _
  calc
    _ = (∑ m∈G,E m)+(∑ m∈S\G,E m) := by
      rw [add_comm]
      exact (sum_sdiff hGS).symm
    _ ≤ _ := add_le_add hbulk hedge

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorHighBand.lean; sha256 a1f345cd92965679752e323f6d531bc7d7449ea4d24e951ce01770f091c64a21 -/
section
/- Research auxiliary, not the registered theorem. The integral-cover proof adapts
FrontierBand.actualIntegralBound from the accepted BV-band module, preserving its
Apache-2.0 provenance (muxkin, wzhxzkk and OpenAI sources credited in that module).
Changes: arbitrary real width Q and arbitrary subset D; no signed-monotonicity step. -/

open Finset MeasureTheory GoldbachMajorArc GoldbachBDH
open scoped Interval
namespace InnerFloorResearch

def realBandSet (Q : ℝ) (n A B : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, A<q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ Q/((q:ℝ)*n)}

theorem subsetIntegralBound (Q : ℝ) (n A B : ℕ) (D : Set ℝ)
    (hQ : 0 ≤ Q) (hA : 1≤A) (hB : 0<B) (hn : 2≤n)
    (hsub : D ⊆ realBandSet Q n A B) :
    ‖∫ t in (0:ℝ)..1, D.indicator
        (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤
      2*(Q/((A:ℝ)*n))*(((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
  classical
  let g := fun t => ‖primeSum n t‖^2
  have cg : Continuous g := by dsimp [g,primeSum,phase]; fun_prop
  let R := Q/((A:ℝ)*n)
  have hR : 0≤R := by dsimp [R]; exact div_nonneg hQ (by positivity)
  let center := fun q a : ℕ => (a:ℝ)/q
  let F := fun (q a : ℕ) => (Set.Icc (center q a-R) (center q a+R)).indicator g
  have hF (q a : ℕ) : Integrable (F q a) volume :=
    (cg.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hp (q a : ℕ) (t : ℝ) : 0≤F q a t := by
    by_cases h : t ∈ Set.Icc (center q a-R) (center q a+R)
    · simpa only [F, Set.indicator_of_mem h] using sq_nonneg ‖primeSum n t‖
    · simp [F,h]
  let G := fun t => ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, F q a t
  have hGi : Integrable G volume := integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun a _ => hF q a
  have hGp (t : ℝ) : 0≤G t := sum_nonneg fun q _ => sum_nonneg fun a _ => hp q a t
  have hdom (t : ℝ) : ‖D.indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ ≤ G t := by
    by_cases ht : t∈D
    · rw [Set.indicator_of_mem ht,norm_mul,norm_pow,bandPhase_norm,mul_one]
      obtain ⟨q,a,haq,hqb,ha,hcop,hnear⟩ := hsub ht
      have hq : q∈Finset.Icc 1 B := mem_Icc.mpr ⟨by omega,hqb⟩
      have ha' : a∈num q := by
        refine mem_filter.mpr ⟨mem_range.mpr ?_,hcop⟩
        by_contra! hh
        have heq := Nat.le_antisymm ha hh
        have := (Nat.coprime_self q).mp (heq ▸ hcop)
        omega
      have hrad : Q/((q:ℝ)*n) ≤ R :=
        div_le_div_of_nonneg_left hQ (by positivity) (by gcongr)
      have htF : t∈Set.Icc (center q a-R) (center q a+R) := by
        have h := abs_le.mp (hnear.trans hrad)
        change center q a-R ≤ t ∧ t ≤ center q a+R
        dsimp [center] at *
        constructor <;> linarith [h.1,h.2]
      change g t ≤ _
      calc
        _ = F q a t := (Set.indicator_of_mem htF g).symm
        _ ≤ ∑ b ∈ num q, F q b t := single_le_sum (fun b _ => hp q b t) ha'
        _ ≤ _ := single_le_sum (fun r _ => sum_nonneg fun b _ => hp r b t) hq
    · simpa [ht] using hGp t
  have htranslate (q a : ℕ) :
      (∫ t, F q a t) = ∫ β in -R..R, g (β+center q a) := by
    rw [intervalIntegral.integral_comp_add_right,intervalIntegral.integral_of_le (by linarith)]
    unfold F
    rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
    congr 1 <;> congr 1 <;> ring
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖D.indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t, G t := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hGi.integrableOn (Filter.Eventually.of_forall hdom)).trans
        (setIntegral_le_integral hGi (Filter.Eventually.of_forall hGp))
    _ = ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, ∫ β in -R..R, g (β+center q a) := by
      unfold G
      rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun a _ => hF q a)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_finsetSum _ (fun a _ => hF q a)]
      simp_rw [htranslate]
    _ = ∫ β in -R..R, ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, g (β+center q a) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro q _
        rw [intervalIntegral.integral_finsetSum]
        exact fun a _ => (cg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
      · intro q _
        apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => cg.comp (continuous_id.add continuous_const)
    _ ≤ ∫ _β in -R..R, (((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
          cg.comp (continuous_id.add continuous_const)
      · exact continuous_const.intervalIntegrable _ _
      · exact fun t _ => shifted_spectrum n B hB t
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; dsimp [R]; ring


theorem subsetBound (Q : ℝ) (n A B : ℕ) (D : Set ℝ)
    (hQ : 0≤Q) (hA : 1≤A) (hB : 0<B) (hBn : B^2≤n) (hn : 2≤n)
    (hsub : D ⊆ realBandSet Q n A B) :
    ‖∫ t in (0:ℝ)..1, D.indicator
        (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤
      24*(n:ℝ)*Q*(1+Real.log n)^2/A := by
  have h := subsetIntegralBound Q n A B D hQ hA hB hn hsub
  have he := energy_bound n (by omega)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  have hx : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : (0:ℝ)<A := by exact_mod_cast (show 0<A by omega)
  have hc : (n:ℝ)+1+(B:ℝ)^2 ≤ 3*n := by
    have hb : (B:ℝ)^2 ≤ n := by exact_mod_cast hBn
    linarith [show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)]
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have he' : weightEnergy n ≤ 3*n*Real.log n := he.trans (by gcongr)
  have he0 : 0≤weightEnergy n := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ _ := h
    _ ≤ 2*(Q/((A:ℝ)*n))*((3*n)*(3*n*Real.log n)) := by
      gcongr
    _ = 18*(n:ℝ)*Q*Real.log n/A := by field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ ha.le
      have he'' : 18*Real.log n ≤ 24*(1+Real.log n)^2 := by nlinarith [sq_nonneg (Real.log (n:ℝ))]
      nlinarith only [mul_le_mul_of_nonneg_left he'' (mul_nonneg hx.le hQ)]

private theorem highBandLog (n : ℕ) (hn : 2≤n) :
    (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
  have hb := Real.natLog_le_logb (n+2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2:ℝ)≤n := by exact_mod_cast hn
  have hh : (n:ℝ)+2 ≤ (n:ℝ)^2 := by nlinarith [mul_nonneg (show 0≤(n:ℝ)-2 by linarith) (show 0≤(n:ℝ)+1 by linarith)]
  have hl := Real.log_le_log (by positivity : 0<(n:ℝ)+2) hh
  rw [Real.log_pow] at hl
  norm_num at hl
  have hx' := (le_div_iff₀ (by linarith : 0<Real.log 2)).mp hb
  have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_)
  linarith only [hl,hx',hm]


open Filter
open scoped Topology

/-- The part with denominators above n^(1/5) has absolute mass o(n), even after
an arbitrary additional mask. The remaining lower-denominator part is not addressed. -/
theorem highBandLittleO (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Set ℝ,
      D ⊆ realBandSet ((Nat.log 2 (n+2):ℝ)^2 * (n:ℝ)^(1/6:ℝ)) n
        ⌊(n:ℝ)^(1/5:ℝ)⌋₊ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ →
      ‖∫ t in (0:ℝ)..1, D.indicator
          (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤ e*(n:ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/5)).comp ht
  have hc := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ)<1/30)).comp_tendsto ht).bound
    (by positivity : 0 < e/4000)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    hp.eventually_ge_atTop 2,hc] with n hn hL hu hsmall
  intro D hD
  let L := Real.log (n:ℝ)
  let u := (n:ℝ)^(1/5:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  let Q := (Nat.log 2 (n+2):ℝ)^2 * v
  let A : ℕ := ⌊u⌋₊
  let B : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hX : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hu2 : 2≤u := hu
  have hA : 1≤A := Nat.floor_pos.mpr (by linarith : 1≤u)
  have hAp : (0:ℝ)<A := by exact_mod_cast hA
  have hA1 : (1:ℝ)≤A := by exact_mod_cast hA
  have huA : u ≤ 2*(A:ℝ) := by
    have hf := Nat.lt_floor_add_one u
    change u < (A:ℝ)+1 at hf
    linarith
  have hB : 0<B := Nat.floor_pos.mpr (Real.one_le_rpow hX (by norm_num))
  have hBsq : B^2≤n := FrontierBand.denomSquare n hn _ (by norm_num)
  have hv : 0≤v := Real.rpow_nonneg hnR.le _
  have hQ : 0≤Q := mul_nonneg (sq_nonneg _) hv
  have hlog := highBandLog n hn
  have hlogSq := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_) hlog 2
  have hQb : Q ≤ 16*L^2*v := by
    have h := mul_le_mul_of_nonneg_right hlogSq hv
    dsimp [Q,L] at *
    nlinarith only [h]
  have hL1 : 1≤L := hL
  have hLsq : (1+L)^2 ≤ 4*L^2 := by nlinarith
  have hmul := mul_le_mul hQb hLsq (sq_nonneg _) (by positivity : 0≤16*L^2*v)
  have hs : L^4 ≤ (e/4000)*(n:ℝ)^(1/30:ℝ) := by
    change ‖Real.log (n:ℝ)^(4:ℝ)‖ ≤ (e/4000)*‖(n:ℝ)^(1/30:ℝ)‖ at hsmall
    simpa only [L,Real.rpow_ofNat,Real.norm_of_nonneg (by positivity : 0≤(Real.log (n:ℝ))^4),
      Real.norm_of_nonneg (Real.rpow_nonneg hnR.le (1/30:ℝ))] using hsmall
  have hpow : (n:ℝ)^(1/30:ℝ)*v = u := by
    dsimp [u,v]
    rw [← Real.rpow_add hnR]
    norm_num
  have hbudget : 24*Q*(1+L)^2 ≤ e*(A:ℝ) := by
    calc
      _ ≤ 1536*L^4*v := by nlinarith only [hmul]
      _ ≤ 1536*((e/4000)*(n:ℝ)^(1/30:ℝ))*v := by gcongr
      _ = (1536/4000:ℝ)*e*u := by rw [← hpow]; ring
      _ ≤ e*(A:ℝ) := by
        nlinarith only [mul_le_mul_of_nonneg_left huA he.le,
          mul_nonneg he.le (Nat.cast_nonneg A : (0:ℝ)≤A)]
  have hbound := subsetBound Q n A B D hQ hA hB hBsq hn hD
  refine hbound.trans ?_
  apply (div_le_iff₀ hAp).2
  have h := mul_le_mul_of_nonneg_right hbudget hnR.le
  dsimp [L] at h
  nlinarith only [h]

end InnerFloorResearch

end

/-! BEGIN InnerFloorFrozenAssembly.lean; sha256 23dcd603a10fcbf4bc40776248d12be290fba988edec319953a77538a30fec6a -/
section
open Finset MeasureTheory Filter
open scoped Interval Topology Classical

namespace InnerFloorResearch

noncomputable section
set_option maxHeartbeats 2000000

/-- The exact registered type at origin/main 1fe24b28926c. -/
def FrozenWideRemainderInnerFloor : Prop :=
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
  let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
  let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
  let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t)
  let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  let H := fun n : ℕ => 256 * Q₁ n * Q n
  let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
  let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
  let lowPart := fun n : ℕ => lowWideArcs n \ arcs n
  let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n
  let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}
  let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re
  let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n)
  floor (fun n => remainder n ∩ inner n)

/-- The only analytic input in this assembly is the actual reduced-cell
model error. It is not the earlier overstrong all-residue variance. -/
def MiddleCellEnergySmall : Prop := ∀ᶠ n : ℕ in atTop,
  mediumCellEnergy n (innerCutoff n) (middleCutoff n) (innerWidth n) ≤
    8*(n:ℝ)/(Real.log (n:ℝ))^4

private theorem mediumIntegral_split {n Q A B : ℕ} {u : ℝ}
    (hn : 0 < n) (hu : 0 ≤ u) (hQA : Q ≤ A) (hAB : A ≤ B)
    (hsep : 2*u*(B : ℝ) < (n : ℝ)) :
    mediumIntegral n Q B u = mediumIntegral n Q A u + mediumIntegral n A B u := by
  let D := mediumBand Q A u (n : ℝ)
  let E := mediumBand A B u (n : ℝ)
  have hd : Disjoint D E := by
    rw [Set.disjoint_left]
    intro t ht ht'
    obtain ⟨q,a,hq,_,hqA,_,hc,ht⟩ := ht
    obtain ⟨r,b,hr,_,hrB,_,hd,ht'⟩ := ht'
    have hh := mediumBand_unique Q B u (n : ℝ) hu (by exact_mod_cast hn)
      hsep hq (hQA.trans_lt hr) (hqA.trans hAB) hrB hc hd ht ht'
    omega
  have hset : mediumBand Q B u (n : ℝ) = D ∪ E := by
    ext t
    constructor
    · rintro ⟨q,a,hq,hq0,hqB,ha,hc,ht⟩
      by_cases hqA : q ≤ A
      · exact Or.inl ⟨q,a,hq,hq0,hqA,ha,hc,ht⟩
      · exact Or.inr ⟨q,a,lt_of_not_ge hqA,hq0,hqB,ha,hc,ht⟩
    · rintro (⟨q,a,hq,hq0,hqA,ha,hc,ht⟩ | ⟨q,a,hq,hq0,hqB,ha,hc,ht⟩)
      · exact ⟨q,a,hq,hq0,hqA.trans hAB,ha,hc,ht⟩
      · exact ⟨q,a,hQA.trans_lt hq,hq0,hqB,ha,hc,ht⟩
  let f := GoldbachGRHApproximation.integrand n
  have hf : Continuous f := by
    unfold f GoldbachGRHApproximation.integrand GoldbachFourthMoment.primeSum GoldbachFourthMoment.phase
    fun_prop
  have hI (s : Set ℝ) (hs : MeasurableSet s) : IntervalIntegrable (s.indicator f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 <|
      (hf.intervalIntegrable 0 1).1.indicator hs
  have hind : (D ∪ E).indicator f = fun t => D.indicator f t + E.indicator f t := by
    ext t
    by_cases hD : t ∈ D
    · have hE : t ∉ E := fun h => Set.disjoint_left.mp hd hD h
      simp [Set.indicator, hD, hE]
    · by_cases hE : t ∈ E <;> simp [Set.indicator, hD, hE]
  unfold mediumIntegral
  rw [hset, hind]
  exact intervalIntegral.integral_add
    (hI D (measurable_mediumBand n Q A u)) (hI E (measurable_mediumBand n A B u))

private theorem signedDifferenceSmall (hEnergy : MiddleCellEnergySmall) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖mediumIntegral n (innerCutoff n) (middleCutoff n) (innerWidth n) -
          mediumModel n (innerCutoff n) (middleCutoff n) (innerWidth n)‖ ≤ ε*(n : ℝ) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventualInnerGeometry, hEnergy,
    ht.eventually_ge_atTop (max 1 (18/ε))] with n hg hv hL
  obtain ⟨hn, hQ, hQA, hAB, huH, hbudget⟩ := hg
  let L := Real.log (n : ℝ)
  let u := innerWidth n
  let A := middleCutoff n
  let Q := innerCutoff n
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLe : 18/ε ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hu : 0 ≤ u := by unfold u innerWidth; positivity
  have hsep : 2*u*(A : ℝ) < (n : ℝ) := by
    apply lt_of_le_of_lt _ hbudget
    gcongr
  have hun : u ≤ (n : ℝ) := by
    have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hQ.trans hQA
    nlinarith only [hsep, mul_le_mul_of_nonneg_left hA1 hu, hu]
  have hE : mediumCellEnergy n Q A u ≤ 8*(n : ℝ)/L^4 := hv
  have H := signedMediumDifference (Q := Q) hn hu hsep (show 0 < 1/L^3 by positivity)
  change ‖_‖ ≤ (1+1/(1/L^3))*mediumCellEnergy n Q A u + (1/L^3)*((n : ℝ)+1)*L^2 at H
  calc
    _ ≤ _ := H
    _ ≤ (1+1/(1/L^3))*(8*(n : ℝ)/L^4) + (1/L^3)*((n : ℝ)+1)*L^2 := by gcongr
    _ ≤ 18*(n : ℝ)/L := by
      have h3 : 1 ≤ L^3 := one_le_pow₀ hL1
      have hb : (1+1/(1/L^3))*(8*(n : ℝ)/L^4) ≤ 16*(n : ℝ)/L := by
        rw [one_div_one_div]
        calc
          _ ≤ (2*L^3)*(8*(n:ℝ)/L^4) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by field_simp <;> ring
      have hc : (1/L^3)*((n : ℝ)+1)*L^2 ≤ 2*(n : ℝ)/L := by
        rw [show (1/L^3)*((n : ℝ)+1)*L^2 = ((n : ℝ)+1)/L by field_simp <;> ring]
        exact div_le_div_of_nonneg_right (by linarith) hL0.le
      exact (add_le_add hb hc).trans_eq (by ring)
    _ ≤ _ := by
      apply (div_le_iff₀ hL0).2
      have he := (div_le_iff₀ hε).1 hLe
      nlinarith only [mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (n : ℝ))]

/-- The exact frozen type follows if the middle-band cell energy input is
proved. The two signed contributions are combined using the disjoint union. -/
theorem candidate_of_middleCellEnergy (hEnergy : MiddleCellEnergySmall) :
    FrozenWideRemainderInnerFloor := by
  have hFun : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Even n → -(ε*(n : ℝ)) ≤
        (∫ t in (0 : ℝ)..1,
          ((((arcSet (outerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n) \
            (arcSet (innerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n)) ∩
            arcSet (outerCutoff n) (innerWidth n) n).indicator
              (GoldbachGRHApproximation.integrand n)) t).re := by
    intro ε hε
    let e := ε/3
    have he : 0 < e := by unfold e; positivity
    obtain ⟨K, hK⟩ := realWidthModelFloor e he
    filter_upwards [eventualInnerGeometry, GoldbachGRHConcreteFloor.eventually_narrow_ge K,
      signedDifferenceSmall hEnergy e he, highBandLittleO e he]
      with n hg hlarge hdiff hhigh
    intro hnEven
    obtain ⟨hn,hQ,hQA,hAB,huH,hbud⟩ := hg
    let Q := innerCutoff n
    let A := middleCutoff n
    let B := outerCutoff n
    let H := (GoldbachGRHBudget.width n : ℝ)
    let u := innerWidth n
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hu : 0 < u := by
      unfold u innerWidth
      exact mul_pos (by exact_mod_cast hQ) (Real.rpow_pos_of_pos hnR _)
    have huQ : (Q : ℝ) ≤ u := by
      unfold u innerWidth
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hn1 (by norm_num))
    have hQB : Q ≤ B := hQA.trans hAB
    have hB₁ : (1 : ℝ) ≤ B := by exact_mod_cast (hQ.trans hQB)
    have hsep : 2*u*(B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      gcongr
    have hun : 2*u ≤ (n : ℝ) := by
      nlinarith only [hsep, mul_le_mul_of_nonneg_left hB₁ (show 0 ≤ 2*u by positivity)]
    have hmask : u*(Q : ℝ)+H*(B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      have hprod : u*(Q : ℝ) ≤ H*(B : ℝ) :=
        mul_le_mul huH (by exact_mod_cast hQB) (Nat.cast_nonneg _) (hu.le.trans huH)
      linarith only [hprod]
    rw [inner_remainder_eq Q B (Q : ℝ) H u (n : ℝ) (huQ.trans huH) huH hnR.le,
      masked_medium_eq Q B u H (n : ℝ) hu.le huH hnR hmask]
    change -(ε*(n : ℝ)) ≤ (mediumIntegral n Q B u).re
    rw [mediumIntegral_split (by omega) hu.le hQA hAB hsep, Complex.add_re]
    have hM := hK n Q A (by omega) hnEven hQ hlarge hQA u hu hun
    have hD : |(mediumIntegral n Q A u - mediumModel n Q A u).re| ≤ e*(n : ℝ) :=
      (Complex.abs_re_le_norm _).trans hdiff
    have hHigh' : ‖mediumIntegral n A B u‖ ≤ e*(n : ℝ) := by
      have hu' : u = (Nat.log 2 (n+2) : ℝ)^2 * (n : ℝ)^(1/6 : ℝ) := by
        unfold u innerWidth innerCutoff GoldbachGRHBudget.narrow
        push_cast <;> rfl
      have H := hhigh (mediumBand A B u n) (by
        intro t ht
        obtain ⟨q,a,hq,_,hqB,ha,hcop,ht⟩ := ht
        exact ⟨q,a,hq,hqB,ha,hcop,hu' ▸ ht⟩)
      exact H
    have hHigh := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hHigh')
    have hD' := neg_le_of_abs_le hD
    rw [Complex.sub_re] at hD'
    unfold e at hM hD' hHigh
    linarith only [hM, hD', hHigh]
  intro ε hε
  exact Filter.eventually_atTop.mp (hFun ε hε)

/-- One-sided signed middle-band floor: strictly weaker than the L2 energy
    hypothesis `MiddleCellEnergySmall`, preserving all sign cancellation
    between the prime sum and the principal model. -/
def SignedMiddleRemainderFloor : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Even n →
    -(ε * (n : ℝ)) ≤
      (mediumIntegral n (innerCutoff n) (middleCutoff n) (innerWidth n) -
        mediumModel n (innerCutoff n) (middleCutoff n) (innerWidth n)).re

/-- Unconditional reduction of the exact frozen statement
    `FrozenWideRemainderInnerFloor` to the one-sided signed middle-band floor
    (without requiring the two-sided L2 bound `MiddleCellEnergySmall`). -/
theorem candidate_of_signedMiddleFloor (hSigned : SignedMiddleRemainderFloor) :
    FrozenWideRemainderInnerFloor := by
  have hFun : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Even n → -(ε * (n : ℝ)) ≤
        (∫ t in (0 : ℝ)..1,
          ((((arcSet (outerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n) \
            (arcSet (innerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n)) ∩
            arcSet (outerCutoff n) (innerWidth n) n).indicator
              (GoldbachGRHApproximation.integrand n)) t).re := by
    intro ε hε
    let e := ε / 3
    have he : 0 < e := by unfold e; positivity
    obtain ⟨K, hK⟩ := realWidthModelFloor e he
    filter_upwards [eventualInnerGeometry, GoldbachGRHConcreteFloor.eventually_narrow_ge K,
      hSigned e he, highBandLittleO e he]
      with n hg hlarge hdiff hhigh
    intro hnEven
    obtain ⟨hn, hQ, hQA, hAB, huH, hbud⟩ := hg
    let Q := innerCutoff n
    let A := middleCutoff n
    let B := outerCutoff n
    let H := (GoldbachGRHBudget.width n : ℝ)
    let u := innerWidth n
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hu : 0 < u := by
      unfold u innerWidth
      exact mul_pos (by exact_mod_cast hQ) (Real.rpow_pos_of_pos hnR _)
    have huQ : (Q : ℝ) ≤ u := by
      unfold u innerWidth
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hn1 (by norm_num))
    have hQB : Q ≤ B := hQA.trans hAB
    have hB₁ : (1 : ℝ) ≤ B := by exact_mod_cast (hQ.trans hQB)
    have hsep : 2 * u * (B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      gcongr
    have hun : 2 * u ≤ (n : ℝ) := by
      nlinarith only [hsep, mul_le_mul_of_nonneg_left hB₁ (show 0 ≤ 2 * u by positivity)]
    have hmask : u * (Q : ℝ) + H * (B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      have hprod : u * (Q : ℝ) ≤ H * (B : ℝ) :=
        mul_le_mul huH (by exact_mod_cast hQB) (Nat.cast_nonneg _) (hu.le.trans huH)
      linarith only [hprod]
    rw [inner_remainder_eq Q B (Q : ℝ) H u (n : ℝ) (huQ.trans huH) huH hnR.le,
      masked_medium_eq Q B u H (n : ℝ) hu.le huH hnR hmask]
    change -(ε * (n : ℝ)) ≤ (mediumIntegral n Q B u).re
    rw [mediumIntegral_split (by omega) hu.le hQA hAB hsep, Complex.add_re]
    have hM := hK n Q A (by omega) hnEven hQ hlarge hQA u hu hun
    have hD' := hdiff hnEven
    rw [Complex.sub_re] at hD'
    have hHigh' : ‖mediumIntegral n A B u‖ ≤ e * (n : ℝ) := by
      have hu' : u = (Nat.log 2 (n + 2) : ℝ) ^ 2 * (n : ℝ) ^ (1 / 6 : ℝ) := by
        unfold u innerWidth innerCutoff GoldbachGRHBudget.narrow
        push_cast <;> rfl
      have H := hhigh (mediumBand A B u n) (by
        intro t ht
        obtain ⟨q, a, hq, _, hqB, ha, hcop, ht⟩ := ht
        exact ⟨q, a, hq, hqB, ha, hcop, hu' ▸ ht⟩)
      exact H
    have hHigh := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hHigh')
    unfold e at hM hD' hHigh
    linarith only [hM, hD', hHigh]
  intro ε hε
  exact Filter.eventually_atTop.mp (hFun ε hε)

#print axioms candidate_of_signedMiddleFloor

end
end InnerFloorResearch
end
