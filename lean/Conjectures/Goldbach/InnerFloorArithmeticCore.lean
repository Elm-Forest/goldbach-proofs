import Mathlib

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
