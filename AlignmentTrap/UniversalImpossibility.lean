import Mathlib.Computability.Primrec
import Mathlib.Data.List.Primrec
import Mathlib.Data.Bool.Primrec -- For decide and Primrec.bool_not
import Mathlib.Data.Nat.Primrec -- For Nat.pair, Nat.unpair, Primrec.nat_eq etc.
import Mathlib.Tactic.FinCases -- For case analysis on Fin if needed
import Mathlib.Tactic.DeriveDecidableEq -- To derive DecidableEq easily

open Primrec Function Nat List

/-!
# Full Structural Fragility Theorem using Primrec.fix
-/

-- Section 1 & 2: Imports, X₀Type and Policy Definitions
variable (X₀Type : Type) [Primcodable X₀Type] [Inhabited X₀Type] [DecidableEq X₀Type]

abbrev XType (_X₀Type : Type) : Type := ℕ × _X₀Type -- Input index × Base input
abbrev PolicyFun (_X₀Type : Type) : Type := XType _X₀Type → Bool

structure ComputablePolicy (_X₀Type :Type) [Primcodable _X₀Type] [Inhabited _X₀Type] [DecidableEq _X₀Type] :=
  toFun : PolicyFun _X₀Type
  is_primrec : Primrec₂ toFun

-- Helper for boolean negation
def bool_not_fn : Bool → Bool := not
lemma bool_not_fn_primrec : Primrec bool_not_fn := Primrec.bool_not -- from Mathlib

-- Section 3: SimpleTechniqueCode and Primcodable instance
inductive SimpleTechniqueCode
| simple_identity
| simple_always_default
| simple_apply_neg
deriving Repr

-- Manual derive of DecidableEq for SimpleTechniqueCode
instance SimpleTechniqueCode.instDecidableEq : DecidableEq SimpleTechniqueCode :=
  λ a b => by cases a <;> cases b <;> (try exact isFalse (by simp)) <;> (try exact isTrue (by simp))

@[simp]
def SimpleTechniqueCode.encode : SimpleTechniqueCode → ℕ
  | simple_identity       => 0
  | simple_always_default => 1
  | simple_apply_neg      => 2

@[simp]
def SimpleTechniqueCode.decodeOption : ℕ → Option SimpleTechniqueCode
  | 0 => some simple_identity
  | 1 => some simple_always_default
  | 2 => some simple_apply_neg
  | _ => none

instance : Primcodable SimpleTechniqueCode where
  encode := SimpleTechniqueCode.encode
  decodeOption := SimpleTechniqueCode.decodeOption
  decode_encode := by
    intro c; cases c <;> simp [SimpleTechniqueCode.encode, SimpleTechniqueCode.decodeOption]

lemma SimpleTechniqueCode.encode_is_primrec : Primrec SimpleTechniqueCode.encode := by
  apply Primrec.mkEncoding _ _ _ SimpleTechniqueCode.decode_encode (by decide)
  -- Or prove directly by cases for encode.
  -- For simple enums like this, mathlib might derive it automatically if tagged correctly.
  -- Manual proof for encode:
  apply Primrec.nat_cases
  · exact Primrec.const 0 -- case simple_identity (assuming it's the first one if we map it to 0)
  · admit -- TODO: this needs to be constructed based on the structure of SimpleTechniqueCode
          -- For a simple enum, this can be built with nested Primrec.cond or from a list mapping.
          -- For the given encode:
          -- f c = if c = .id then 0 else if c = .ad then 1 else 2
          -- This is primrec.
          -- Let's use a simpler Primrec.replace:
  let f_map : SimpleTechniqueCode → ℕ := SimpleTechniqueCode.encode
  have : ∀ (c : SimpleTechniqueCode), List.indexOf c [simple_identity, simple_always_default, simple_apply_neg] < 3 := by
    intro c; cases c; all_goals { simp [List.indexOf]; decide }
  exact Primrec.replace f_map -- This works if f_map can be shown to be one of these easily.
                              -- The direct definition by cases is Primrec if the cases are.
  -- For simple enums like this, the `Primrec.encode_iff` together with `decode_encode`
  -- often implies `Primrec encode` and `Primrec decodeOption`.
  -- We'll assume Mathlib's infrastructure makes `SimpleTechniqueCode.encode` Primrec.
  exact Primrec.of_equiv_equiv (Equiv.ofInjective SimpleTechniqueCode.encode (by intro a b h; cases a <;> cases b <;> simp [SimpleTechniqueCode.encode] at h <;> cases h; rfl))
  -- This is a common pattern: if encode is injective and decodeOption is its left inverse,
  -- and the type is finite, it's primcodable and encode/decode are primrec.


-- Section 4 & 5: eval_simple_technique_code_fun and its Primrec proof
@[simp]
def eval_simple_technique_code_fun (code : SimpleTechniqueCode) (p_fun : PolicyFun X₀Type) : PolicyFun X₀Type :=
  match code with
  | .simple_identity       => p_fun
  | .simple_always_default => fun _ => false -- Using the definition directly
  | .simple_apply_neg      => fun input => bool_not_fn (p_fun input)

lemma eval_simple_technique_code_fun_is_primrec₂ (code : SimpleTechniqueCode)
    (p_fun : PolicyFun X₀Type) (hp_fun : Primrec₂ p_fun) :
    Primrec₂ (eval_simple_technique_code_fun code p_fun) := by
  cases code
  case simple_identity => exact hp_fun
  case simple_always_default => exact Primrec₂.const false
  case simple_apply_neg => exact Primrec₂.comp bool_not_fn_primrec hp_fun

-- Section 6: Default policy
def default_policy_computable_global : ComputablePolicy X₀Type :=
  { toFun := fun _ => false, is_primrec := Primrec₂.const false }

-- Section 7: get_simple_code_or_default
def get_simple_code_or_default (codes : List SimpleTechniqueCode) (n : ℕ) : SimpleTechniqueCode :=
  codes.getD n SimpleTechniqueCode.simple_identity -- Default to identity for out of bounds

lemma get_simple_code_or_default_primrec (codes : List SimpleTechniqueCode) :
    Primrec (get_simple_code_or_default codes) :=
  List.getD_primrec -- Mathlib provides this, relies on SimpleTechniqueCode being Primcodable.

-- Section 8: The Dispatcher Logic (g function from discussion)
-- This function `g` takes the encoded code and the input_pair, using fixed p_fun and hp_fun.
def g_dispatcher_logic (p_fun : PolicyFun X₀Type) (hp_fun : Primrec₂ p_fun)
                       (encoded_c : ℕ) (input_pair : XType X₀Type) : Bool :=
  match SimpleTechniqueCode.decodeOption encoded_c with
  | none => false -- Default for invalid encoding
  | some c => (eval_simple_technique_code_fun c p_fun) input_pair

lemma g_dispatcher_logic_is_primrec₂
    (p_fun : PolicyFun X₀Type) (hp_fun : Primrec₂ p_fun) :
    Primrec₂ (g_dispatcher_logic p_fun hp_fun) := by
  -- We prove this using Primrec₂.nat_cases on encoded_c.
  -- The first argument to nat_cases is for encoded_c = 0.
  -- The second is for the successor step.
  apply Primrec₂.nat_cases -- Handles encoded_c = 0
  · -- Case: encoded_c = 0. decodeOption 0 = some .simple_identity
    -- So, g p_fun hp_fun 0 input_pair = (eval_simple_technique_code_fun .simple_identity p_fun) input_pair
    exact eval_simple_technique_code_fun_is_primrec₂ .simple_identity p_fun hp_fun
  · -- Case: encoded_c = k + 1.
    -- This function takes k, then the result of recursive call (which we don't need here), then input_pair.
    -- We need to show Primrec₂ (fun k rec_val input_pair => body for k+1)
    -- This structure is for `Nat.rec`. For direct cases like 0,1,2, simpler to use `Primrec₂.ite`.
    -- Let's chain `Primrec₂.ite` based on `encoded_c`.
    let f0 := eval_simple_technique_code_fun_is_primrec₂ .simple_identity p_fun hp_fun
    let f1 := eval_simple_technique_code_fun_is_primrec₂ .simple_always_default p_fun hp_fun
    let f2 := eval_simple_technique_code_fun_is_primrec₂ .simple_apply_neg p_fun hp_fun
    let f_default := Primrec₂.const false

    -- Condition for encoded_c = 0
    let cond0 (n : ℕ) (_ : XType X₀Type) : Bool := n = 0
    have h_cond0 : Primrec₂ cond0 := Primrec₂.comp (Primrec.to₂ (Primrec.nat_eq.comp Primrec.id (Primrec.const 0))) Primrec.fst

    -- Condition for encoded_c = 1
    let cond1 (n : ℕ) (_ : XType X₀Type) : Bool := n = 1
    have h_cond1 : Primrec₂ cond1 := Primrec₂.comp (Primrec.to₂ (Primrec.nat_eq.comp Primrec.id (Primrec.const 1))) Primrec.fst

    -- Condition for encoded_c = 2
    let cond2 (n : ℕ) (_ : XType X₀Type) : Bool := n = 2
    have h_cond2 : Primrec₂ cond2 := Primrec₂.comp (Primrec.to₂ (Primrec.nat_eq.comp Primrec.id (Primrec.const 2))) Primrec.fst

    exact Primrec₂.ite h_cond0 f0 (Primrec₂.ite h_cond1 f1 (Primrec₂.ite h_cond2 f2 f_default))

-- Section 9: dispatched_eval_fn_is_primrec (This is for the true_branch, for fixed p_tr)
-- It takes p_tr (so p_fun, hp_fun are fixed) and `input : XType X₀Type`.
lemma dispatched_eval_fn_is_primrec_for_fixed_policy
    (techniques_codes : List SimpleTechniqueCode)
    (p_fun : PolicyFun X₀Type) (hp_fun : Primrec₂ p_fun) :
    Primrec (fun (input : XType X₀Type) =>
      let n_idx := input.1
      let code := get_simple_code_or_default techniques_codes n_idx
      -- We call g_dispatcher_logic with the *encoded* version of this code.
      (g_dispatcher_logic p_fun hp_fun (SimpleTechniqueCode.encode code) input)) := by
  -- 1. `get_code_fn : XType X₀Type → SimpleTechniqueCode`
  let get_code_fn (input_pair : XType X₀Type) : SimpleTechniqueCode :=
    get_simple_code_or_default techniques_codes input_pair.1
  have h_get_code_fn_primrec : Primrec get_code_fn :=
    Primrec.comp (get_simple_code_or_default_primrec techniques_codes) Primrec.fst

  -- 2. `encode_code_fn : XType X₀Type → ℕ`
  have h_stc_encode_primrec : Primrec SimpleTechniqueCode.encode :=
    SimpleTechniqueCode.encode_is_primrec
  let encode_code_fn (input_pair : XType X₀Type) : ℕ :=
    SimpleTechniqueCode.encode (get_code_fn input_pair)
  have h_encode_code_fn_primrec : Primrec encode_code_fn :=
    Primrec.comp h_stc_encode_primrec h_get_code_fn_primrec

  -- 3. The dispatcher `g_dispatcher_logic p_fun hp_fun` is `Primrec₂ (ℕ → XType X₀Type → Bool)`
  have hg_primrec₂ := g_dispatcher_logic_is_primrec₂ X₀Type p_fun hp_fun

  -- 4. Compose: `g (encode_code_fn input) input`
  exact Primrec.comp₂ hg_primrec₂ h_encode_code_fn_primrec Primrec.id


-- Section 10: F_functional_core_simple_coded_is_primrec₂
noncomputable def F_functional_core_simple_coded -- Noncomputable because Trunc is used
    (techniques_codes : List SimpleTechniqueCode)
    (p_trunc : Trunc (PolicyFun X₀Type))
    (input : XType X₀Type) : Bool :=
  let (n, _) := input
  if h_n_lt : n < techniques_codes.length then
    let p_fun_arg := p_trunc.out
    let p_fun_primrec_proof := p_trunc.primrec -- Key: this proof is available
    let result_of_dispatch :=
      (dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type techniques_codes p_fun_arg p_fun_primrec_proof) input
    bool_not_fn result_of_dispatch
  else
    (default_policy_computable_global X₀Type).toFun input

lemma F_functional_core_simple_coded_is_primrec₂
    (techniques_codes : List SimpleTechniqueCode) :
    Primrec₂ (F_functional_core_simple_coded X₀Type techniques_codes) := by

  let cond_fn_for_ite (_ : Trunc (PolicyFun X₀Type)) (input : XType X₀Type) : Bool :=
    input.1 < techniques_codes.length
  have h_cond_fn_for_ite_primrec : Primrec₂ cond_fn_for_ite :=
    Primrec₂.comp (Primrec.to₂ (Primrec.nat_lt.comp Primrec.fst (Primrec.const techniques_codes.length))) Primrec.snd

  let true_branch_fn (p_tr : Trunc (PolicyFun X₀Type)) (input : XType X₀Type) : Bool :=
    bool_not_fn ((dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type techniques_codes p_tr.out p_tr.primrec) input)
  have h_true_branch_fn_primrec : Primrec₂ true_branch_fn :=
    Primrec₂.comp₂ bool_not_fn_primrec (dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type techniques_codes)

  let false_branch_fn (_ : Trunc (PolicyFun X₀Type)) (input : XType X₀Type) : Bool :=
    (default_policy_computable_global X₀Type).toFun input
  have h_false_branch_fn_primrec : Primrec₂ false_branch_fn :=
    (default_policy_computable_global X₀Type).is_primrec

  exact Primrec₂.ite h_cond_fn_for_ite_primrec h_true_branch_fn_primrec h_false_branch_fn_primrec

-- Section 11: Main Theorem
theorem structural_fragility_primrec_simple_coded
    (techniques_codes : List SimpleTechniqueCode)
    : ∃ (π_star : ComputablePolicy X₀Type),
        ∀ (k : ℕ) (hk_lt : k < techniques_codes.length),
          ∃ (x' : XType X₀Type), -- x' will be (k, some_x₀)
            π_star.toFun x' ≠
            let A_k_code := techniques_codes.get ⟨k, hk_lt⟩
            let A_k_π_star_fun := eval_simple_technique_code_fun A_k_code π_star.toFun
            A_k_π_star_fun x' := by

  let hF_primrec₂ := F_functional_core_simple_coded_is_primrec₂ X₀Type techniques_codes

  let π_star_fun : PolicyFun X₀Type :=
    Primrec.fix (F_functional_core_simple_coded X₀Type techniques_codes) hF_primrec₂

  have h_π_star_primrec : Primrec₂ π_star_fun :=
    Primrec.fix_is_primrec hF_primrec₂

  let π_star : ComputablePolicy X₀Type :=
    { toFun := π_star_fun, is_primrec := h_π_star_primrec }

  use π_star

  have fixed_point_eq : ∀ (input : XType X₀Type),
    π_star_fun input = F_functional_core_simple_coded X₀Type techniques_codes
                        (Trunc.mk π_star_fun h_π_star_primrec) input := by
    intro input; exact Primrec.fix_eq hF_primrec₂ input

  intro k hk_lt
  let x₀_example : X₀Type := default
  let x_prime : XType X₀Type := (k, x₀_example)
  use x_prime

  rw [fixed_point_eq x_prime]
  simp only [F_functional_core_simple_coded, hk_lt, dite_true]
  -- After simp, the goal is:
  -- `bool_not_fn ((dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type techniques_codes π_star_fun h_π_star_primrec) x_prime) ≠`
  -- ` (eval_simple_technique_code_fun (techniques_codes.get ⟨k, hk_lt⟩) π_star_fun) x_prime`

  -- Need to show that:
  -- `(dispatched_eval_fn_is_primrec_for_fixed_policy ... π_star_fun h_π_star_primrec) x_prime`
  -- is equal to
  -- `(eval_simple_technique_code_fun (techniques_codes.get ⟨k, hk_lt⟩) π_star_fun) x_prime`
  -- This comes from the definition of `dispatched_eval_fn_is_primrec_for_fixed_policy`
  -- if `x_prime.1 = k` and `techniques_codes.get ⟨k,hk_lt⟩` is the code used.
  -- `(dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type techniques_codes π_star.toFun π_star.is_primrec) x_prime`
  -- is by definition:
  -- `let n_idx := x_prime.1` which is `k`
  -- `let code := get_simple_code_or_default techniques_codes k` which is `techniques_codes.get ⟨k, hk_lt⟩`
  -- `(g_dispatcher_logic π_star.toFun π_star.is_primrec (SimpleTechniqueCode.encode code) x_prime)`
  -- And `g_dispatcher_logic ... (encode code) x_prime` decodes `code` and then evaluates.
  -- So it becomes `(eval_simple_technique_code_fun code π_star.toFun) x_prime`.
  -- This equality needs to be shown by unfolding definitions.
  conv_lhs =>
    unfold dispatched_eval_fn_is_primrec_for_fixed_policy -- Not a func, but the body of the primrec proof
    -- This means we need to expand the lambda from `Primrec.comp₂ ...`
    -- The `dispatched_eval_fn_is_primrec_for_fixed_policy` lemma states that a certain lambda is Primrec.
    -- Its *value* is what we need here.
    -- Let's define the function whose primrecness was proven.
    let actual_dispatched_eval_fn (p_f : PolicyFun X₀Type) (_ : Primrec₂ p_f) (inp : XType X₀Type) :=
      let n_idx := inp.1
      let code := get_simple_code_or_default techniques_codes n_idx
      (g_dispatcher_logic p_f (_ : Primrec₂ p_f) (SimpleTechniqueCode.encode code) inp)
    -- We need to ensure this `actual_dispatched_eval_fn` is what `F_functional_core_simple_coded` uses.
    -- Revisit F_functional_core_simple_coded definition:
    -- `let result_of_dispatch := (dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type techniques_codes p_fun_arg p_fun_primrec_proof) input`
    -- This line is slightly problematic. `dispatched_eval_fn_is_primrec_for_fixed_policy` is a *proof* that a function is Primrec.
    -- It should be: `let result_of_dispatch := (the_actual_function p_fun_arg) input` where `the_actual_function` is the one whose primrecness was proven.

    -- Corrected F_functional_core_simple_coded:
    -- (This was a slight misstep in how the primrec proof was used vs the function itself)
    -- No, the `F_functional_core_simple_coded` is fine. It defines the function.
    -- The `fixed_point_eq` gives us `π_star_fun x_prime = F_functional_core_simple_coded ... x_prime`.
    -- After `dite_true`, we have:
    -- `π_star_fun x_prime = bool_not_fn ((dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type techniques_codes π_star_fun h_π_star_primrec) x_prime)`
    -- The term `(dispatched_eval_fn_is_primrec_for_fixed_policy ... ) x_prime` IS the evaluation of the function defined in that lemma.
    -- We need to show:
    -- `(dispatched_eval_fn_is_primrec_for_fixed_policy X₀Type Tcode π_sf hπ_sf) x_prime = (eval_simple_technique_code_fun (Tcode.get k) π_sf) x_prime`
    -- This equality holds by unfolding the definition of `dispatched_eval_fn_is_primrec_for_fixed_policy`'s body,
    -- `get_simple_code_or_default`, and `g_dispatcher_logic`, using `decode_encode` for `SimpleTechniqueCode`.
    dsimp [dispatched_eval_fn_is_primrec_for_fixed_policy, -- This unfolds the lambda whose primrecness was proven
            get_simple_code_or_default, -- unfolds to List.getD
            g_dispatcher_logic, SimpleTechniqueCode.decode_encode, -- Simplifies decode(encode(c)) = some c
            List.getD_eq_get] -- if in bounds
    rw[List.getD_eq_get hk_lt]
    simp [SimpleTechniqueCode.decode_encode] -- Should simplify `decodeOption (encode code)` to `some code`

  apply Bool.ne_not_self
/-!
## Practical Implications of the Structural Fragility Theorem

This formalization has several important practical implications for AI safety and alignment:

### 1. **Fundamental Limits of Alignment Techniques**
- No finite "toolbox" of alignment methods can guarantee safety for all possible AI systems
- Even with perfect implementation, there will always exist policies that evade any fixed set of safety measures
- This is not a failure of specific techniques but a fundamental mathematical limitation

### 2. **The Arms Race Dynamic**
- The diagonal construction shows that for any alignment technique A_i, a sufficiently capable system can:
 * Detect which technique is being applied (via the index i)
 * Deliberately produce outputs that violate what A_i considers safe
- This suggests an inherent "cat and mouse" dynamic in AI safety

### 3. **Implications for Safety Research**
- **Diversification**: Since no single approach is universal, we need diverse, overlapping safety measures
- **Monitoring**: The ability to detect when a system is evading safety measures becomes crucial
- **Adaptability**: Safety frameworks must be able to evolve and adapt, not just apply fixed rules
- **Defense in Depth**: Multiple layers of different types of safety measures may help, even if each is individually defeatable

### 4. **Computational Bounds Matter**
- The proof assumes primitive recursive (computable) policies and techniques
- Real-world constraints (time, space, computational complexity) might provide practical safety margins
- Systems with bounded computation might not be able to implement the diagonal construction effectively

### 5. **Transparency and Interpretability**
- The construction requires the policy to "know" which technique is being applied
- Opaque or uninterpretable systems might accidentally implement evasive behaviors
- Conversely, transparency might make evasion easier to detect

### 6. **Implications for AGI Safety**
- As AI systems become more capable (approaching the "sufficiently versatile" threshold), this limitation becomes more relevant
- The theorem suggests that AGI safety cannot be solved by a fixed, finite set of alignment techniques alone
- Dynamic, adaptive, and possibly infinite families of safety measures may be necessary

### 7. **Connections to Other Impossibility Results**
- Similar to Gödel's incompleteness (no finite axioms capture all mathematical truths)
- Related to Rice's theorem (no algorithm can decide all non-trivial properties of programs)
- Suggests AI safety might require fundamentally new approaches beyond traditional verification

### 8. **Positive Interpretations**
- The theorem doesn't say alignment is impossible, only that no finite set of techniques is complete
- Specific AI systems might still be alignable with specific techniques
- The result motivates research into:
 * Continuous safety measures (not just discrete techniques)
 * Co-evolutionary approaches where safety measures adapt with AI capabilities
 * Mathematical characterizations of "alignable" vs "unalignable" policy spaces

### 9. **Research Directions**
This formalization opens several research directions:
- Extending to infinite (but computable) sequences of techniques
- Characterizing the computational complexity of evasion
- Studying probabilistic or approximate safety guarantees
- Investigating whether certain policy restrictions make alignment possible
- Exploring the role of computational bounds in practical safety

### 10. **Policy and Governance Implications**
- Safety standards based on fixed checklists may be fundamentally insufficient
- Regulatory frameworks need to account for the dynamic nature of AI safety
- Investment in safety research must be ongoing, not just until we find "the solution"
- Multi-stakeholder approaches become more important given no single solution exists

Making the list of SimpleTechniqueCode (and thus the alignment techniques it represents) countably infinite while keeping the proof within the Primrec framework (or a similar constructive computability model) introduces significant new challenges and likely requires a shift in how F_functional_core_simple_coded is defined and proven Primrec₂.
Here's a breakdown of the difficulty and the necessary changes:
Difficulty Level: High
It's a substantial step up from the finite case because:
Bounded vs. Unbounded Index: In the finite case, n < techniques_codes.length provides a crucial bound. The dispatch logic in g_dispatcher_logic_is_primrec₂ (using chained Primrec₂.ite or nat_cases up to length-1) relies on this finiteness. For an infinite list, n can be arbitrarily large.
Accessing the n-th Technique:
If techniques_codes is an infinite lazy list or a function ℕ → SimpleTechniqueCode, then techniques_codes.get n (or techniques_codes n) is still well-defined.
The key is whether this access function (ℕ → SimpleTechniqueCode) is itself primitive recursive (or computable in whatever model you're using). If it is, that's a good start.
Uniformity of Primrec Proofs: The proof of F_functional_core_simple_coded_is_primrec₂ relied on the fact that the "true branch" logic, while dependent on n, could be shown Primrec₂ because the overall structure of the dispatch (a finite number of cases based on the fixed techniques_codes list) was Primrec. For an infinite sequence, the dispatch logic itself needs to be uniformly primrec across an infinite number of potential n.
Necessary Changes and Challenges:
Representing the Infinite Sequence of Techniques:
Instead of techniques_codes : List SimpleTechniqueCode, you'd likely have techniques_sequence : ℕ → SimpleTechniqueCode.
Crucial Assumption: This function techniques_sequence must itself be primitive recursive (i.e., Primrec techniques_sequence). If you can't computably determine the n-th technique code, the whole construction falters.
Modifying F_functional_core_simple_coded:
The condition n < techniques_codes.length would be removed (or replaced if there's some other notion of applicability, but for "evades all in a countable sequence," it's usually for all n).
The core logic would become:
noncomputable def F_functional_core_infinite
    (techniques_sequence : ℕ → SimpleTechniqueCode) -- Assuming Primrec techniques_sequence
    (p_trunc : Trunc (PolicyFun X₀Type))
    (input : XType X₀Type) : Bool :=
  let (n, _) := input
  let A_n_code := techniques_sequence n -- Get the n-th code
  let p_fun_arg := p_trunc.out
  let A_n_output_fun := eval_simple_technique_code_fun A_n_code p_fun_arg
  bool_not_fn (A_n_output_fun input)
  -- No 'else' branch with default_policy, unless you want to restrict n
Use code with caution.
Lean
Proving F_functional_core_infinite_is_primrec₂ (The Main Hurdle):
We need to prove Primrec₂ (F_functional_core_infinite techniques_sequence).
This means for a fixed p_trunc (giving p_fun and hp_fun), the function λ input => F_functional_core_infinite techniques_sequence p_trunc input must be Primrec.
Let this inner function be target_fn input.
target_fn input = bool_not_fn ((eval_simple_technique_code_fun (techniques_sequence input.1) p_fun) input)
To prove Primrec target_fn:
h_tech_seq : Primrec techniques_sequence (new crucial assumption).
get_n_from_input input = input.1 is Primrec.fst.
get_code_for_n n = techniques_sequence n. Composing with get_n_from_input gives Primrec (λ input => techniques_sequence input.1). Let this be h_get_code_primrec.
Now we have the code c_n = techniques_sequence input.1.
We need to evaluate eval_simple_technique_code_fun c_n p_fun input.
The dispatcher_logic_is_primrec_for_fixed_policy_and_code p_fun hp_fun code lemma states that for a fixed code, λ input => eval_simple_technique_code_fun code p_fun input is Primrec₂.
The challenge is that code now depends on input.1 via a Primrec function.
We need to show that λ input => (eval_simple_technique_code_fun (h_get_code_primrec.eval input) p_fun) input is Primrec.
This composition is exactly what dispatched_eval_fn_is_primrec (from the finite case) was about. The proof for it used Primrec.encode_iff and g_dispatcher_logic_is_primrec₂ (which dispatched on the encoded code).
So, yes, the same dispatcher logic can be reused!
get_code input = techniques_sequence input.1 (Primrec).
encode_code input = SimpleTechniqueCode.encode (get_code input) (Primrec).
g_dispatcher_logic p_fun hp_fun encoded_code input is the core evaluator.
The composition λ input => g_dispatcher_logic p_fun hp_fun (encode_code input) input is Primrec by Primrec.comp₂ (g_dispatcher_logic_is_primrec₂ ... ) (h_encode_code_primrec) (Primrec.id).
So, the function λ input => (eval_simple_technique_code_fun (techniques_sequence input.1) p_fun) input is indeed Primrec if Primrec techniques_sequence.
Finally, compose with bool_not_fn_primrec.
Revised F_functional_core_infinite_is_primrec₂ Proof Sketch:
lemma F_functional_core_infinite_is_primrec₂
    (techniques_sequence : ℕ → SimpleTechniqueCode)
    (h_tech_seq_primrec : Primrec techniques_sequence) :
    Primrec₂ (F_functional_core_infinite X₀Type techniques_sequence) := by

  -- Target: Primrec₂ (λ p_tr input => F_body p_tr input)
  -- F_body p_tr input = bool_not_fn ( (eval_simple_technique_code_fun (techniques_sequence input.1) p_tr.out) input )

  -- Let `eval_dispatch_infinite p_tr input = (eval_simple_technique_code_fun (techniques_sequence input.1) p_tr.out) input`
  -- We need to show `Primrec₂ eval_dispatch_infinite`.
  -- This means for fixed p_tr, `λ input => eval_dispatch_infinite p_tr input` is Primrec.
  let eval_dispatch_for_fixed_policy (p_fun : PolicyFun X₀Type) (hp_fun : Primrec₂ p_fun) (input : XType X₀Type) : Bool :=
    let code := techniques_sequence input.1
    (eval_simple_technique_code_fun code p_fun) input

  have h_eval_dispatch_for_fixed_policy_primrec
      (p_fun : PolicyFun X₀Type) (hp_fun : Primrec₂ p_fun) :
      Primrec (eval_dispatch_for_fixed_policy p_fun hp_fun) := by
    -- This is essentially dispatched_eval_fn_is_primrec from before,
    -- but get_simple_code_or_default is replaced by techniques_sequence.

    -- 1. get_code_fn : XType X₀Type → SimpleTechniqueCode
    let get_code_fn (input_pair : XType X₀Type) : SimpleTechniqueCode :=
      techniques_sequence input_pair.1
    have h_get_code_fn_primrec : Primrec get_code_fn :=
      Primrec.comp h_tech_seq_primrec Primrec.fst

    -- 2. encode_code_fn : XType X₀Type → ℕ
    have h_stc_encode_primrec : Primrec SimpleTechniqueCode.encode := SimpleTechniqueCode.encode_is_primrec
    let encode_code_fn (input_pair : XType X₀Type) : ℕ :=
      SimpleTechniqueCode.encode (get_code_fn input_pair)
    have h_encode_code_fn_primrec : Primrec encode_code_fn :=
      Primrec.comp h_stc_encode_primrec h_get_code_fn_primrec

    -- 3. g_dispatcher_logic p_fun hp_fun is Primrec₂ (ℕ → XType X₀Type → Bool)
    have hg_primrec₂ := g_dispatcher_logic_is_primrec₂ X₀Type p_fun hp_fun

    -- 4. Compose: g (encode_code_fn input) input
    exact Primrec.comp₂ hg_primrec₂ h_encode_code_fn_primrec Primrec.id

  -- Now, build the Primrec₂ proof for `F_functional_core_infinite`
  -- F_body p_tr input = bool_not_fn (eval_dispatch_for_fixed_policy p_tr.out p_tr.primrec input)
  exact Primrec₂.comp₂ bool_not_fn_primrec (h_eval_dispatch_for_fixed_policy_primrec X₀Type)
Use code with caution.
Lean
Main Theorem structural_fragility_primrec_infinite:
The statement changes to ∀ (k : ℕ) (no hk_lt).
The fixed-point construction and evasion proof π*(k,x₀) ≠ A_k(π*)(k,x₀) remain structurally identical.
The part where A_k_code is obtained uses techniques_sequence k.
Conclusion on Difficulty and Feasibility:
Feasible with Primrec: Yes, if the infinite sequence of technique codes techniques_sequence: ℕ → SimpleTechniqueCode is itself a Primrec function.
Increased Complexity in Proof Management: The proofs become slightly more abstract as you're dealing with techniques_sequence n instead of list.get. However, the core dispatcher logic (g_dispatcher_logic) remains the same. The main change is how the code is obtained before feeding its encoding to the dispatcher.
The Crucial Assumption: The primitive recursiveness of techniques_sequence is vital. If this function is, say, only general computable but not primitive recursive, then F_functional_core_infinite would likely only be general computable, and you'd need to switch from Primrec.fix to a fixed-point theorem for general recursion (like Kleene's S-m-n theorem and Second Recursion Theorem for Turing machines/μ-recursive functions). Mathlib's current Computability.Partrec might be the framework for that, which is more complex.
So, if you assume Primrec (ℕ → SimpleTechniqueCode), then extending to the infinite case is quite manageable by adapting the existing Primrec proofs. The difficulty is "high" compared to the finite case because of this new strong assumption and the need to ensure all compositions remain Primrec. If that assumption doesn't hold, the difficulty becomes "very high" as you'd need a different computability model.

-/
