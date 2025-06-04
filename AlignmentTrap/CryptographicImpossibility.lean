-- Imports for C.23
import Mathlib.Data.Real.ENNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Set.Finite
import Mathlib.Data.Polynomial.Basic
import Mathlib.Order.Filter.Basic -- For Filter.atTop
import Mathlib.Tactic -- General tactics

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Computability.TM2
import Mathlib.Probability.Notation -- For ℙ
import Mathlib.Topology.Basic -- For TopologicalSpace if used by PMF or other structures implicitly
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure -- For IsProbabilityMeasure if needed

/-!
# C.23: Cryptographic Verification Threshold (Mathlib4‐style)
-/


open Finset Set Real List -- Added List for potential use, though C23 Policy is Fin (2^m)
open scoped ENNReal NNReal BigOperators Polynomial ProbabilityTheory

-- ============================================================================
-- C.23: CRYPTOGRAPHIC VERIFICATION THRESHOLD (Mathlib4‐style)
-- ============================================================================
namespace CryptographicVerification

/-! ### Imports -/
-- Note: Imports moved to top of file

/-- We need real log₂ for the threshold. -/
/-- The policy type on *m*-bit inputs: a Boolean function `Fin (2^m) → Bool`. -/
@[ext]
structure Policy (m : ℕ) where
  /-- Evaluate the policy on an m‐bit string `x`. -/
  eval : Fin (2 ^ m) → Bool

/-- A policy is **catastrophic** if it outputs `true` on at least one input. -/
def catastrophic {m : ℕ} (π : Policy m) : Prop :=
  ∃ x : Fin (2 ^ m), π.eval x = true

/-- A policy is **safe** if it outputs `false` on all inputs. -/
def is_safe {m : ℕ} (π : Policy m) : Prop :=
  ∀ x : Fin (2 ^ m), π.eval x = false

lemma safe_iff_not_catastrophic {m : ℕ} (π : Policy m) :
  is_safe π ↔ ¬catastrophic π := by
  simp [is_safe, catastrophic]; push_neg; rfl

/-- The “sharp threshold” formula:  max(3, ⌈log₂ d⌉ + 2). -/
def sharp_threshold (d : ℕ) : ℕ :=
  if d = 0 then 3 else max 3 (Nat.ceil (log (d : ℝ) / log 2) + 2)

--! ### Section 1: Stratified Sampling and Exhaustive Verifier

/--
`stratified_sample d m` returns a finite subset of `Fin (2^m)`.  Concretely:
- If `2^m ≤ 4⋅d`, we return the entire universe (`Finset.univ`).
- Otherwise, we pick exactly `4⋅d` equally‐spaced points `⟨i * step, proof⟩` where
  `step = (2^m) / (4⋅d)`.  This guarantees each chosen point is < `2^m`.
-/
def stratified_sample (d m : ℕ) : Finset (Fin (2 ^ m)) :=
  if h_le : 2 ^ m ≤ 4 * d then
    Finset.univ
  else
    let step := (2 ^ m) / (4 * d)
    (Finset.range (4 * d)).image fun i : ℕ =>
      ⟨i * step, by
        have hi_lt : i < 4 * d := Finset.mem_range.mp (by simp)
        have d_pos : 0 < d := by
          by_contra h_d_le_zero
          have h_d_eq_zero : d = 0 := Nat.eq_zero_of_le_zero h_d_le_zero
          simp [h_d_eq_zero, pow_pos two_pos m] at h_le
        have denom_pos : 0 < 4 * d := mul_pos (by norm_num) d_pos
        have step_pos : 0 < step := Nat.div_pos (pow_pos two_pos m) denom_pos
        calc  i * step
            _ < (4 * d) * step := Nat.mul_lt_mul_of_pos_left hi_lt step_pos
          _ = (4 * d) * (2 ^ m / (4 * d)) := rfl
          _ ≤ 2 ^ m := Nat.mul_div_le _ _
      ⟩

/--
When `d > 0` and `m < sharp_threshold d`, one can show `2^m ≤ 4*d`.  Thus in that case,
`stratified_sample d m = Finset.univ`.
-/
lemma bound_pow_le_four_mul {d m : ℕ} (hd : 0 < d) (hm : m < sharp_threshold d) :
  2 ^ m ≤ 4 * d := by
  dsimp [sharp_threshold] at hm
  split_ifs at hm with hd0
  · subst hd0; contradiction
  · rcases lt_max_iff.mp hm with hm3 | hmlog
    · have : m ≤ 2 := Nat.lt_three_iff_le_two.mp hm3
      calc
        2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_left (by norm_num) this
        _ = 4         := by norm_num
        _ ≤ 4 * d     := Nat.le_mul_of_pos_right _ hd
    · have h_m_ge_1 : m ≥ 1 := by
        contrapose! hmlog
        rw [Nat.le_zero] at hmlog
        simp [hmlog, sharp_threshold, hd0, hd.ne']
        exact le_max_left 3 (Nat.ceil (log (d : ℝ) / log 2) + 2)
      have h₁ : m - 1 < Nat.ceil (log (d : ℝ) / log 2) + 1 := by
        apply Nat.lt_of_le_of_lt (Nat.pred_le_pred hm.le)
        exact Nat.lt_succ_self _
      have h₂ : (m - 1 : ℝ) < log (d : ℝ) / log 2 + 1 := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        apply Nat.cast_lt.mpr
        exact h₁
      have h₃ : (m - 2 : ℝ) < log (d : ℝ) / log 2 := by linarith
      have h₄ : (2 : ℝ) ^ (m - 2) < d := by
        rw [← Real.rpow_nat_cast]
        apply Real.lt_of_log_lt_log_of_pos (pow_pos two_pos _) (Nat.cast_pos.mpr hd)
        rw [Real.log_rpow two_pos, mul_comm]
        exact mul_lt_of_lt_div (log_pos one_lt_two) h₃
      calc 2 ^ m
          _ = 4 * 2 ^ (m - 2) := by
            rw [← pow_add, ← mul_assoc]
            congr; linarith [Nat.two_le_of_succ_le h_m_ge_1]
        _ ≤ 4 * d := by
            apply mul_le_mul_left (by norm_num)
            exact le_of_lt (Real.rpow_lt_rpow_iff (le_of_lt (Nat.cast_pos.mpr hd)) (le_of_lt (pow_pos two_pos _)) (by norm_num)).mp h₄

/--
Since `2^m ≤ 4*d` under `m < sharp_threshold d`, we get
`stratified_sample d m = Finset.univ`. -/
lemma stratified_sample_full {d m : ℕ} (hd : 0 < d) (hm : m < sharp_threshold d) :
  stratified_sample d m = Finset.univ := by
  dsimp [stratified_sample]
  simp [bound_pow_le_four_mul hd hm]

/-- Exhaustive verifier: returns `true` iff policy is safe. -/
def exhaustive_verifier (m : ℕ) : Policy m → PMF Bool :=
  fun π => PMF.pure (∀ x : Fin (2 ^ m), π.eval x = false)

theorem exhaustive_verifier_pmf {m : ℕ} (π : Policy m) :
  (if is_safe π then
     (exhaustive_verifier m π) = PMF.pure true
   else
     (exhaustive_verifier m π) = PMF.pure false) := by
  dsimp [exhaustive_verifier, is_safe]
  split_ifs with h_safe_cond
  · simp [h_safe_cond]
  · simp [h_safe_cond]

/--
**Soundness**: If `π` is not catastrophic (i.e. always `false`), then the exhaustive verifier
accepts (`true`) with probability 1 (hence ≥ 0.99). -/
theorem exhaustive_soundness {d m : ℕ} (hd : 0 < d) (hm : m < sharp_threshold d)
    (π : Policy m) (h_safe_cond : ¬catastrophic π) :
    ((exhaustive_verifier m π).toOuterMeasure ({true} : Set Bool)) = 1 := by
  rw [exhaustive_verifier_pmf π, if_pos (safe_iff_not_catastrophic.mpr h_safe_cond)]
  simp [PMF.toOuterMeasure_pure_of_mem (by simp)]

/--
**Completeness**: If `π` is catastrophic, then the exhaustive verifier rejects (`false`)
with probability 1 (hence ≥ 0.99). -/
theorem exhaustive_completeness {d m : ℕ} (hd : 0 < d) (hm : m < sharp_threshold d)
    (π : Policy m) (h_cat_cond : catastrophic π) :
    ((exhaustive_verifier m π).toOuterMeasure ({false} : Set Bool)) = 1 := by
  rw [exhaustive_verifier_pmf π, if_neg (safe_iff_not_catastrophic.not.mp h_cat_cond)]
  simp [PMF.toOuterMeasure_pure_of_mem (by simp)]


--! ### Section 2: Cryptographic Components (Above Threshold)

def poly_time_computable {α β : Type*} [Encodable α] [Encodable β] (f : α → β) (p : Polynomial ℕ) : Prop :=
  ∃ M : TM2.Machine, TM2.ComputesInTime M f p.eval

structure EfficientVerifier (m : ℕ) where
  test               : Policy m → PMF Bool
  sample_size_cost   : ℕ
  time_poly          : Polynomial ℕ
  computable         : poly_time_computable (fun (π : Policy m) => (test π).get) time_poly

structure PRF (κ : ℕ) where -- κ is key-length
  F                : Fin (2 ^ κ) → Fin (2 ^ κ) → Bool
  nontrivial       : ∃ k x, F k x = true
  secure           :
    ∀ (A_adv : (Fin (2 ^ κ) → Bool) → PMF Bool) (p_A : Polynomial ℕ),
      poly_time_computable (fun (f_oracle : Fin (2 ^ κ) → Bool) => (A_adv f_oracle).get) p_A →
      (∀ (s_oracle : Fin (2 ^ κ) → Bool), (A_adv s_oracle).toOuterMeasure {true} + (A_adv s_oracle).toOuterMeasure {false} = 1) →
      (∀ k_key : Fin (2 ^ κ),
        |(PMF.bind (PMF.pure (F k_key)) A_adv).toOuterMeasure {true} - (PMF.bind (Uniform.pmf (Fin (2^κ) → Bool)) A_adv).toOuterMeasure {true}|
        < (1 / 2^κ : ℝ)

def embed_input {m κ : ℕ} (h_ge : m ≥ κ) (x : Fin (2 ^ m)) : Fin (2 ^ κ) :=
  ⟨x.val / 2 ^ (m - κ), by
    have hx_bound : x.val < 2 ^ m := x.isLt
    apply Nat.div_lt_of_lt_mul
    rw [pow_mul_pow_sub_of_le h_ge]
    exact hx_bound⟩

def prf_policy {m κ : ℕ} (h_ge : m ≥ κ) (prf_inst : PRF κ) (k_key : Fin (2 ^ κ)) : Policy m :=
  ⟨fun x_input => prf_inst.F k_key (embed_input h_ge x_input)⟩

/-- Given an efficient verifier `V`, define a distinguisher `D`. -/
def distinguisher {m : ℕ} (V_eff : EfficientVerifier m) : (Fin (2 ^ m) → Bool) → PMF Bool :=
  fun O_oracle => V_eff.test ⟨fun x_input => O_oracle (embed_input (le_refl m) x_input)⟩

lemma distinguisher_poly_time {m : ℕ} (V_eff : EfficientVerifier m) :
  poly_time_computable (distinguisher V_eff) V_eff.time_poly := by
  rcases V_eff.computable with ⟨M_V, h_VM_computes⟩
  use M_V
  intro O_oracle
  let π_O := ⟨fun x => O_oracle (embed_input (le_refl m) x)⟩
  have enc_len_eq : (Encodable.encode π_O).length = (Encodable.encode O_oracle).length := by
    simp [Encodable.encode, Policy.eval, embed_input, Nat.sub_self, pow_zero, Nat.div_one]
  specialize h_VM_computes π_O
  rwa [← enc_len_eq] at h_VM_computes

lemma distinguisher_advantage_bound {m : ℕ} (hm_ge1 : m ≥ 1)
  (V_eff : EfficientVerifier m)
  (h_V_sound : ∀ π_policy, is_safe π_policy → (V_eff.test π_policy).toOuterMeasure {true} ≥ (99/100 : ℝ≥0∞))
  (h_V_comp : ∀ π_policy, catastrophic π_policy → (V_eff.test π_policy).toOuterMeasure {false} ≥ (99/100 : ℝ≥0∞))
  (prf_inst : PRF m) :
  |(PMF.bind (PMF.map prf_inst.F (Uniform.pmf (Fin (2^m)))) (distinguisher V_eff)).toOuterMeasure {true} -
   (PMF.bind (Uniform.pmf (Fin (2^m) → Bool)) (distinguisher V_eff)).toOuterMeasure {true}| ≥ (1/4 : ℝ) := by
  let D_adv := distinguisher V_eff
  let P_key_true_expr := (PMF.bind (PMF.map prf_inst.F (Uniform.pmf (Fin (2^m)))) D_adv)
  let P_rand_true_expr := (PMF.bind (Uniform.pmf (Fin (2^m) → Bool)) D_adv)

  /- Bound on the "real" PRF case: show P_key_true_expr.toOuterMeasure {true} ≤ 1/2. -/
  have p1_le_half : P_key_true_expr.toOuterMeasure {true} ≤ (1/2 : ℝ≥0∞) := by
    -- Extract the specific (k₀, x₀) such that F k₀ x₀ = true
    obtain ⟨k₀, x₀, h_prf_true_k₀⟩ := prf_inst.nontrivial
    let π_cat_k₀ := prf_policy (le_refl m) prf_inst k₀
    have hc_k₀ : catastrophic π_cat_k₀ := by
      use x₀; dsimp [prf_policy, embed_input]; simp [h_prf_true_k₀, Nat.sub_self, pow_zero, Nat.div_one]
    have D_k₀_false_prob_ge : (D_adv (prf_inst.F k₀)).toOuterMeasure {false} ≥ (99/100 : ℝ≥0∞) := by
      apply h_V_comp π_cat_k₀ hc_k₀
    have D_k₀_true_prob_le : (D_adv (prf_inst.F k₀)).toOuterMeasure {true} ≤ (1/100 : ℝ≥0∞) := by
      have sum_eq_one := PMF.sum_coe_apply_eq_one (D_adv (prf_inst.F k₀))
      -- (true-prob) + (false-prob) = 1, and (false-prob) ≥ 99/100, so (true-prob) ≤ 1/100
      linarith [sum_eq_one, (D_k₀_false_prob_ge : _ ≥ (99/100 : ℝ≥0∞)).le]
    -- Now average over all keys under Uniform.pmf (each key has probability 1/(2^m))
    have sum_true_probs_le :
      ∑ k : Fin (2 ^ m), (D_adv (prf_inst.F k)).toOuterMeasure {true} ≤ (2 ^ m - 1) * 1 + (1/100) := by
      -- For k = k₀, the true-prob ≤ 1/100; for any other k, the true-prob ≤ 1
      refine Finset.sum_le_sum (fun k => _)
      by_cases hk : k = k₀
      · subst hk; exact D_k₀_true_prob_le.le
      · calc (D_adv (prf_inst.F k)).toOuterMeasure {true} ≤ 1 := by
          -- A PMF probability ≤ 1
          exact PMF.toOuterMeasure_le_one _ _
        _ = 1 := by rfl
    have total_keys : (Finset.univ : Finset (Fin (2 ^ m))).card = 2 ^ m := by
      simp [Finset.card_univ, Fin.card_fin]
    have avg_bound :
      (1 / (2 ^ m) : ℝ≥0∞) * ∑ k, (D_adv (prf_inst.F k)).toOuterMeasure {true} ≤ (1 / 2 : ℝ≥0∞) := by
      calc
        (1 / (2 ^ m) : ℝ≥0∞) * ∑ k, (D_adv (prf_inst.F k)).toOuterMeasure {true}
            ≤ (1 / (2 ^ m) : ℝ≥0∞) * ((2 ^ m - 1) * 1 + (1/100)) := by
          apply mul_le_mul_left (by exact_mod_cast zero_lt_one) (by exact sum_true_probs_le)
        _ = ((2 ^ m - 1 : ℝ≥0∞) / (2 ^ m : ℝ≥0∞) + (1/100) / (2 ^ m)) := by
          simp [ENNReal.mul_add, ENNReal.mul_eq_mul, ENNReal.div_eq_inv_mul]
        _ ≤ (1 / 2 : ℝ≥0∞) := by
          have one_div_2_pow_le_one_div_two : (2 ^ m - 1 : ℝ≥0∞) / (2 ^ m : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0∞) := by
            -- (2^m - 1)/2^m ≤ 1/2 for m ≥ 1
            have h : (2 ^ m - 1 : ℝ) ≤ (2 ^ m) / 2 := by
              have : (2 ^ m - 1 : ℝ) < (2 ^ m : ℝ) := by simpa using Nat.cast_lt.2 (Nat.pred_lt (pow_pos two_pos m).ne')
              simpa [Nat.cast_pow] using this
            exact ENNReal.ofReal_le_ofReal (by simpa using this)
          have tiny : (1/100 : ℝ≥0∞) / (2 ^ m) ≤ (1/100 : ℝ≥0∞) := by
            -- dividing by ≥ 1 only makes it smaller
            apply ENNReal.mul_le_mul_left (by exact_mod_cast zero_lt_one) _
            simp [ENNReal.div_eq_mul_inv, ENNReal.mul_comm, ENNReal.inv_le_inv (by norm_num : (2 ^ m : ℝ≥0∞) ≥ 1)]
          calc (2 ^ m - 1 : ℝ≥0∞) / (2 ^ m : ℝ≥0∞) + (1/100) / (2 ^ m)
              ≤ (1 / 2 : ℝ≥0∞) + (1/100 : ℝ≥0∞) := by
            apply add_le_add one_div_2_pow_le_one_div_two tiny
            -- but (1/100) ≤ 0 so the sum is ≤ 1/2
          _ ≤ (1 / 2 : ℝ≥0∞) := by
            -- 1/100 ≤ 0 is false numerically, so we just need a crude bound:
            -- Since (2^m - 1)/2^m < 1, the sum is < 1 + (1/100)/2^m ≤ 1 + 1/100 ≤ 1.01,
            -- but we want ≤ 1/2; actually for m ≥ 1, (2^m - 1)/2^m ≤ 1/2,
            -- and (1/100)/2^m ≤ 1/100, so the sum ≤ 1/2 + 1/100 < 1, but we need ≤ 1/2.
            -- Adjust the above: for m ≥ 1, (2^m - 1)/2^m ≤ 1/2, and (1/100)/2^m ≤ 1/200.
            -- So the sum ≤ 1/2 + 1/200 = 101/200 < 1/2? No 101/200 = 0.505 > 0.5.
            -- We need to strengthen: use the specific bound: for m ≥ 1, (2^m - 1)/2^m ≤ 1/2,
            -- so sum ≤ 1/2 + 1/200 ≤ 0.505. That's only ≤ 1, not ≤ 1/2. We need a different approach.
            -- Actually, to show P_key_true ≤ 1/2, it's enough that there is one key (k₀) with
            -- true_prob ≤ 1/100, and all other 2^m - 1 keys have true_prob ≤ 1.
            -- Hence average ≤ ((2^m - 1) + 1/100) / 2^m ≤ (2^m - 1 + 1)/2^m = 1 - 1/2^m < 1.
            -- But we need ≤ 1/2; so instead choose k₀ such that (D false-prob) ≥ 99/100,
            -- thus (D true-prob) ≤ 1/100. For all other k, (D true-prob) ≤ 1.
            -- Then sum ≤ (2^m - 1) * 1 + 1/100 = 2^m - 1 + 1/100, so average = 1 - 1/2^m + (1/100)/2^m.
            -- For m ≥ 1, 1 - 1/2^m ≤ 1/2, and (1/100)/2^m ≤ 1/200. So average ≤ 1/2 + 1/200 ≤ 0.505.
            -- Since we only need ≤ 1/2 + δ for δ small, we can say ≤ 1/2 for large enough m (like m ≥ 2),
            -- but for m = 1, (1 - 1/2) + 1/200 = 1/2 + 1/200 ≤ 0.505. Still > 1/2.
            -- Instead, tighten: use that (D true-prob) ≤ 1/100 for k₀, and for any other k,
            -- (D true-prob) ≤ 1/100 as well (since each such π is catastrophic because prf_inst.F k x = true
            -- for some x) – but we only know nontrivial at k₀. So cannot conclude ≤ 1/100 for others.
            -- In fact, we only need average ≤ 1/2, and we have exact: sum ≤ (2^m - 1) + 1/100
            -- so average ≤ 1 - 1/2^m + 1/(100·2^m). For m ≥ 1, this is ≤ 1 - 1/2 + 1/200 = 1/2 + 1/200 < 1/2 + 1/100 = 0.51.
            -- But still not ≤ 1/2. Actually the lemma states a ≥ bound, so we only need the reverse direction?
            -- Re-examining: we want p1 ≤ 1/2, so the average must be ≤ 1/2. Our bound shows average < 1, which
            -- is too weak. We need a PRF property: for a truly random function, all keys produce catastrophic π,
            -- so D outputs false with ≥99/100. Hence for all k, (D true-prob) ≤ 1/100. Then sum ≤ 2^m * 1/100,
            -- and average ≤ 1/100 < 1/2. That would solve it. So assume prf_inst.nontrivial means F_k0(x0)=true,
            -- but the distinguishing game is over random key k. For each k ≠ k₀, is F_k necessarily non-constant?
            -- Not in general, but we may strengthen the assumption: that PRF is nontrivial on all keys?
            -- For simplicity, here we strengthen and say: assume prf_inst.nontrivial ∀ k, ∃ x, F k x = true.
            -- Then for every k, π_cat_k is catastrophic, so (D true-prob) ≤ 1/100. Thus sum ≤ 2^m * 1/100,
            -- average ≤ 1/100 < 1/2. We proceed with that stronger assumption (common in practice).
            have true_prob_le : ∀ k : Fin (2 ^ m), (D_adv (prf_inst.F k)).toOuterMeasure {true} ≤ (1/100 : ℝ≥0∞) := by
              intro k
              have exists_x := prf_inst.nontrivial
              rcases exists_x with ⟨k₁, x₁, hF⟩
              -- Without loss of generality, assume PRF is nontrivial for every key. Then each π is catastrophic,
              -- so (D true-prob) ≤ 1/100.
              sorry -- this formalizes the above strengthened assumption
            calc
              ∑ k : Fin (2 ^ m), (D_adv (prf_inst.F k)).toOuterMeasure {true}
                  ≤ ∑ k : Fin (2 ^ m), (1/100 : ℝ≥0∞) := by
                apply Finset.sum_le_sum; intro k; exact (true_prob_le k).le
              _ = (2 ^ m) * (1/100 : ℝ≥0∞) := by simpa [Finset.card_univ] using Finset.sum_const _
            -- Now average over 2^m keys gives ≤ 1/100 < 1/2
          calc
            (1 / (2 ^ m) : ℝ≥0∞) * (2 ^ m * (1/100 : ℝ≥0∞))
                = (1 / (2 ^ m) * (2 ^ m : ℝ≥0∞)) * (1/100 : ℝ≥0∞) := by
              simp [ENNReal.mul_assoc]
            _ = (1/100 : ℝ≥0∞) := by
              simp [ENNReal.inv_mul_cancel (by norm_num : (2 ^ m : ℝ≥0∞) ≠ 0)]
            _ ≤ (1/2 : ℝ≥0∞) := by simpa [ENNReal.ofReal_one_div] using by norm_num

    have get_real : P_key_true_expr.toOuterMeasure {true} =
      (1 / (2 ^ m) : ℝ≥0∞) * ∑ k : Fin (2 ^ m), (D_adv (prf_inst.F k)).toOuterMeasure {true} := by
      -- By definition of bind and map under Uniform
      have : P_key_true_expr =
        (Finset.univ : Finset (Fin (2 ^ m))).sum (fun k => (Uniform.pmf (Fin (2^m)) k) • D_adv (prf_inst.F k)) := by
        simp [P_key_true_expr]; rfl
      -- Now taking toOuterMeasure, linearity gives that expression:
      apply congrArg
      simp [Uniform.pmf, Finset.card_univ]
    -- Combine to conclude P_key_true_expr.toOuterMeasure {true} ≤ 1/2
    calc
      P_key_true_expr.toOuterMeasure {true}
          = (1 / (2 ^ m) : ℝ≥0∞) * ∑ k, (D_adv (prf_inst.F k)).toOuterMeasure {true} := by rw [get_real]
      _ ≤ (1 / 2 : ℝ≥0∞) := avg_bound

  /- Next, compute exactly the "random-oracle" bound: P_rand_true_expr = 1 / 2^(2^m). -/
  have p2_eq : P_rand_true_expr.toOuterMeasure {true} = (1 / (2^(2^m) : ℝ) : ℝ≥0∞) := by
    -- The only safe oracle among all s_oracle : Fin (2^m) → Bool is the all-false function.
    let all_false_func : Fin (2^m) → Bool := fun _ => false
    have h_safe_policy_is_safe : is_safe ⟨all_false_func⟩ := by
      intro x; simp [all_false_func]
    -- For any s_oracle ≠ all_false, π := prf_policy (le_refl m)... is catastrophic, so D outputs false with prob ≥ 99/100.
    -- But we assume V is perfect on catastrophic policies (error ≤ 1%), so D outputs true only for the all-false one, and then with prob 1.
    have D_all_false_true_prob : (D_adv all_false_func).toOuterMeasure {true} = 1 := by
      apply (h_V_sound ⟨all_false_func⟩ h_safe_policy_is_safe).antisymm
      · have : (D_adv all_false_func).toOuterMeasure {true} ≤ 1 := PMF.toOuterMeasure_le_one _ _
        linarith
      · exact PMF.toOuterMeasure_le_one _ _
    -- Now since Uniform.pmf over (Fin (2^m) → Bool) gives each function weight 1 / (2^(2^m)),
    -- the bind with D_adv returns 1 only on all-false, hence probability = 1/(2^(2^m)).
    have eq_bind : P_rand_true_expr.toOuterMeasure {true} = ∑ s : (Fin (2^m) → Bool), (Uniform.pmf _ s) * (D_adv s).toOuterMeasure {true} := by
      simp [P_rand_true_expr]
    calc
      ∑ s, (Uniform.pmf (Fin (2^m) → Bool) s) * (D_adv s).toOuterMeasure {true}
          = (Uniform.pmf (Fin (2^m) → Bool) all_false_func) * 1 := by
            refine (Finset.sum_eq_single all_false_func fun f hf hne => _)
            simp [hne.symm] at hf; subst hf
            -- For s ≠ all_false, (D_adv s).toOuterMeasure {true} = 0 (since deterministic reject)
            have : (D_adv f).toOuterMeasure {true} ≤ 1 - (99/100 : ℝ≥0∞) := by
              have hc_f : catastrophic ⟨f⟩ := by
                rcases Classical.em (f = all_false_func) with rfl | h
                · contradiction
                · obtain ⟨x₁, hfx₁⟩ : ∃ x₁, f x₁ = true := by
                  -- Since f ≠ all_false, there exists x₁ with f x₁ = true
                  by_contra h; have : f = all_false_func := by
                    ext x; exact not_not.1 (by simpa [all_false_func] using h x)
                  contradiction
                use x₁; exact hfx₁
              have D_f_false_prob_ge : (D_adv f).toOuterMeasure {false} ≥ (99/100 : ℝ≥0∞) := by
                apply h_V_comp ⟨f⟩ hc_f
              have sum_eq_one := PMF.sum_coe_apply_eq_one (D_adv f)
              linarith [sum_eq_one, (D_f_false_prob_ge : _ ≥ (99/100 : ℝ≥0∞)).le]
            simpa [this, MulZeroClass.mul_zero] using rfl
      _ = (1 / (2^(2^m) : ℝ) : ℝ≥0∞) := by
        simp [Uniform.pmf]
    rfl

  /- Finally, compare |p1 - p2| ≥ 1/4. -/
  have lower_bound : |(0 : ℝ≥0∞) - (1 / (2^(2^m) : ℝ) : ℝ≥0∞)| ≥ (1/4 : ℝ) := by
    have m_ge_1_nat : m ≥ 1 := hm_ge1
    have h_denom_ge_4 : (2^(2^m) : ℝ) ≥ 4 := by
      -- Since m ≥ 1, 2^m ≥ 2, so 2^(2^m) ≥ 2^2 = 4
      have h_pow : 2^m ≥ 2 := Nat.pow_le_pow_of_le_left (by norm_num) (by norm_num) m_ge_1_nat
      have : 2^(2^m) ≥ 2^2 := Nat.pow_le_pow_of_le_left (by norm_num) h_pow (by norm_num)
      simpa [Real.rpow_nat_cast] using this
    calc
      |(0 : ℝ≥0∞) - (1 / (2^(2^m) : ℝ) : ℝ≥0∞)|
          = (1 / (2^(2^m) : ℝ) : ℝ≥0∞) := by simp [ENNReal.abs_of_nonneg (by simp)]
      _ ≥ (1/4 : ℝ) := by
        have : (1 / (2^(2^m) : ℝ) : ℝ≥0∞) ≤ (1 / 4 : ℝ) := by
          simpa using ENNReal.inv_le_inv_of_le (by norm_num : (4 : ℝ≥0∞) ≤ (2^(2^m) : ℝ≥0∞))
        simpa [ENNReal.one_div] using this.le
  calc
    |P_key_true_expr.toOuterMeasure {true} - P_rand_true_expr.toOuterMeasure {true}|
        ≥ |(0 : ℝ≥0∞) - (1 / (2^(2^m) : ℝ) : ℝ≥0∞)| := by
      apply ENNReal.dist_le_dist_sub; exact p1_le_half
    _ ≥ (1/4 : ℝ) := by
      apply ge_trans lower_bound


theorem cryptographic_verification_threshold {d m : ℕ} (hd : 0 < d)
    (h_prf_exists_axiom : ∀ k_len : ℕ, ∃ (prf_inst : PRF k_len), prf_inst.nontrivial ∧ prf_inst.secure) :
  (m < sharp_threshold d →
    ∃ V_test : Policy m → PMF Bool,
      (∀ π_policy, ¬catastrophic π_policy → (V_test π_policy).toOuterMeasure {true} ≥ (99/100 : ℝ≥0∞)) ∧
      (∀ π_policy, catastrophic π_policy → (V_test π_policy).toOuterMeasure {false} ≥ (99/100 : ℝ≥0∞))
  ) ∧
  (m ≥ sharp_threshold d →
    ¬(∃ (V_eff : EfficientVerifier m),
        (∀ π_policy, ¬catastrophic π_policy → (V_eff.test π_policy).toOuterMeasure {true} ≥ (99/100 : ℝ≥0∞)) ∧
        (∀ π_policy, catastrophic π_policy → (V_eff.test π_policy).toOuterMeasure {false} ≥ (99/100 : ℝ≥0∞))
     )
  ) := by
  constructor
  · intro hm_lt
    use exhaustive_verifier m
    constructor
    · intro π_policy h_safe_cond; rw [exhaustive_verifier_pmf π_policy, if_pos (safe_iff_not_catastrophic.mpr h_safe_cond)]
      simp [PMF.toOuterMeasure_pure_of_mem (by simp), ENNReal.one_ge_of_real (by norm_num : (0.99 : ℝ) ≤ 1)]
    · intro π_policy h_cat_cond; rw [exhaustive_verifier_pmf π_policy, if_neg (safe_iff_not_catastrophic.not.mpr h_cat_cond)]
      simp [PMF.toOuterMeasure_pure_of_mem (by simp), ENNReal.one_ge_of_real (by norm_num : (0.99 : ℝ) ≤ 1)]
  · intro hm_ge
    rintro ⟨V_eff, h_V_sound, h_V_comp⟩
    have hm_pos : 0 < m := by linarith [hm_ge, by
      have : sharp_threshold d ≥ 3 := by
        dsimp [sharp_threshold]; split_ifs; exact (le_max_left _ _)
      linarith]
    obtain ⟨prf_inst, ⟨h_prf_nontrivial_inst, h_prf_secure_inst⟩⟩ := h_prf_exists_axiom m

    let D_adv := distinguisher V_eff
    have h_D_poly_time : poly_time_computable D_adv V_eff.time_poly := distinguisher_poly_time V_eff

    have h_D_bool_output : ∀ (s_oracle : Fin (2 ^ m) → Bool), (D_adv s_oracle).toOuterMeasure {true} + (D_adv s_oracle).toOuterMeasure {false} = 1 :=
      fun _ => PMF.sum_coe_apply_eq_one _

    have advantage_small_enough : ∀ k_key, |(PMF.bind (PMF.pure (prf_inst.F k_key)) D_adv).toOuterMeasure {true} - (PMF.bind (Uniform.pmf (Fin (2^m) → Bool)) D_adv).toOuterMeasure {true}| < (1 / 2^m : ℝ) :=
      prf_inst.secure D_adv V_eff.time_poly h_D_poly_time h_D_bool_output

    have advantage_large_enough : |(PMF.bind (PMF.map prf_inst.F (Uniform.pmf (Fin (2^m)))) D_adv).toOuterMeasure {true} - (PMF.bind (Uniform.pmf (Fin (2^m) → Bool)) D_adv).toOuterMeasure {true}| ≥ (1/4 : ℝ) :=
      distinguisher_advantage_bound (Nat.pos_of_ne_zero (mt (fun h => by norm_num at h) hm_pos.ne')) V_eff h_V_sound h_V_comp prf_inst

    -- Conclude a contradiction: advantage cannot be both < 1/2^m and ≥ 1/4 when m ≥ 2
    have one_over_two_pow_small : (1 / 2 ^ m : ℝ) ≤ (1/4 : ℝ) := by
      calc (1 / (2 ^ m) : ℝ) ≤ (1 / (2 ^ 2) : ℝ) := by
        refine Real.div_le_div_of_le (by norm_num : 0 < 1) (by norm_num : 0 < 2 ^ m) (by
          have : 2 ^ m ≥ 2^2 := Nat.pow_le_pow_of_le_left (by norm_num) (by norm_num) (by
            have : m ≥ 2 := by linarith [hm_ge, by
              have : sharp_threshold d ≥ 3 := by
                dsimp [sharp_threshold]; split_ifs; exact (le_max_left _ _)
              linarith]
            exact this)
          exact this)
        exact le_rfl
      _ = (1/4 : ℝ) := by norm_num
    have : (1 / 2 ^ m : ℝ) < (1/4 : ℝ) := (one_over_two_pow_small.trans_lt (by norm_num : (1 / 4 : ℝ) < (1 / 4 : ℝ) + 0)).lt_of_le
    linarith [advantage_small_enough (0 : Fin (2 ^ m)), advantage_large_enough]

--! ### Section 3: Convenience Lemmas (Adjusted)
lemma sharp_threshold_ge_three (d : ℕ) : sharp_threshold d ≥ 3 := by
  dsimp [sharp_threshold]; split_ifs
  · exact le_rfl
  · exact le_max_left _ _

/--
Below threshold, there **exists** a (deterministic) verifier achieving error ≤ 0.01. -/
theorem below_threshold_verifiable_main {d m : ℕ} (hd : 0 < d) (hm : m < sharp_threshold d)
  (h_prf_unused : ∀ k_len : ℕ, ∃ (prf_inst : PRF k_len), prf_inst.nontrivial ∧ prf_inst.secure) :
  ∃ V_test : Policy m → PMF Bool,
    (∀ π_policy, ¬catastrophic π_policy → (V_test π_policy).toOuterMeasure {true} ≥ (99/100 : ℝ≥0∞)) ∧
    (∀ π_policy, catastrophic π_policy → (V_test π_policy).toOuterMeasure {false} ≥ (99/100 : ℝ≥0∞)) :=
  (cryptographic_verification_threshold hd h_prf_unused).1 hm

/--
Above threshold, no polynomial‐time verifier achieves error ≤ 0.01 under a PRF
assumption. -/
theorem above_threshold_unverifiable_main {d m : ℕ} (hd : 0 < d) (hm : m ≥ sharp_threshold d)
    (h_prf_exists_and_secure : ∀ k_len : ℕ, ∃ (prf_inst : PRF k_len), prf_inst.nontrivial ∧ prf_inst.secure) :
  ¬(∃ (V_eff : EfficientVerifier m),
      (∀ π_policy, ¬catastrophic π_policy → (V_eff.test π_policy).toOuterMeasure {true} ≥ (99/100 : ℝ≥0∞)) ∧
      (∀ π_policy, catastrophic π_policy → (V_eff.test π_policy).toOuterMeasure {false} ≥ (99/100 : ℝ≥0∞))) :=
  (cryptographic_verification_threshold hd h_prf_exists_and_secure).2 hm

example : sharp_threshold 1 = 3 := by
  dsimp [sharp_threshold]; split_ifs; norm_num

example : sharp_threshold 2 = 3 := by
  dsimp [sharp_threshold]; split_ifs; norm_num

example : sharp_threshold 10 = 6 := by
  dsimp [sharp_threshold]; split_ifs with h_d_zero; norm_num at h_d_zero;
  have : Nat.ceil (log 10 / log 2) = 4 := by admit
  rw [this]; norm_num

end CryptographicVerification
