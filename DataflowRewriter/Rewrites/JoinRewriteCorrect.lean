/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Tactic
import DataflowRewriter.Rewrites.JoinRewrite
import Mathlib.Tactic

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace DataflowRewriter.JoinRewrite

open StringModule

abbrev Ident := Nat

-- abbrev S₁ := "S1"
-- abbrev S₂ := "S2"
-- abbrev S₃ := "S3"
variable {T₁ T₂ T₃ : Type}
variable (S₁ S₂ S₃ : String)

@[drunfold_defs]
def lhsNames := ((rewrite.rewrite [S₁, S₂, S₃]).get rfl).input_expr.build_module_names
@[drunfold_defs]
def rhsNames := ((rewrite.rewrite [S₁, S₂, S₃]).get rfl).output_expr.build_module_names

@[drunfold_defs]
def rewriteLhsRhs := rewrite.rewrite [S₁, S₂, S₃] |>.get rfl

def environmentLhs : IdentMap String (TModule1 String) := lhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd
def environmentRhs : IdentMap String (TModule1 String) := rhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd

@[drenv] theorem find?_join1_data : (Batteries.AssocList.find? ("join " ++ S₁ ++ " " ++ S₂) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ T₂⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join " ++ S₁ ++ " " ++ S₂) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₁ ++ " " ++ S₂ == "join " ++ S₁ ++ " " ++ S₂) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data : (Batteries.AssocList.find? ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join (T₁ × T₂) T₃⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join1_data2 : (Batteries.AssocList.find? ("join " ++ S₂ ++ " " ++ S₃) (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₂ T₃⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == "join " ++ S₂ ++ " " ++ S₃) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == "join " ++ S₂ ++ " " ++ S₃) = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₂ ++ " " ++ S₃ == "join " ++ S₂ ++ " " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data2 : (Batteries.AssocList.find? ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ (T₂ × T₃)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_pure_data2 : (Batteries.AssocList.find? ("pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, pure λ ((a, b, c) : T₁ × (T₂ × T₃)) => ((a, b), c)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

variable (T₁ T₂ T₃) in
def_module lhsModuleType : Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).input_expr, @environmentLhs T₁ T₂ T₃ S₁ S₂ S₃ ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_pure_data2, find?_join2_data2, find?_join2_data, find?_join1_data, find?_join1_data2]
  dsimp

def cast_module_type {α} {f : α → Type _} {s s' : Σ T, f T} (heq : s = s') : f s.1 = f s'.1 := by simp_all

variable (T₁ T₂ T₃) in
def_module lhsModule : StringModule (lhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).input_expr, @environmentLhs T₁ T₂ T₃ S₁ S₂ S₃ ]

variable (T₁ T₂ T₃) in
def_module rhsModuleType : Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).output_expr, @environmentRhs T₁ T₂ T₃ S₁ S₂ S₃ ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_pure_data2, find?_join2_data2, find?_join2_data, find?_join1_data, find?_join1_data2]
  dsimp

variable (T₁ T₂ T₃) in
def_module rhsModule : StringModule (rhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).output_expr, @environmentRhs T₁ T₂ T₃ S₁ S₂ S₃ ]

instance : MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by
  dsimp [rhsModule, lhsModule]
  solve_match_interface

@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

theorem sigma_rw_simp {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by simp [drunfold,drcompute,seval]; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

inductive partially

inductive partially_flushed: lhsModuleType T₁ T₂ T₃ -> Prop where
| lhs: ∀ lower arb, partially_flushed ⟨lower, [], arb⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, arb, []⟩

def ψ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  let ⟨⟨j2l, j2r⟩, ⟨j1l, j1r⟩⟩ := lhs
  let ⟨⟨j2l', j2r'⟩, ⟨⟨j1l', j1r'⟩, p⟩⟩ := rhs
  (j2l.map Prod.fst ++ j1l = p.map (Prod.fst ∘ Prod.fst) ++ j2l') ∧
  (j2l.map Prod.snd ++ j1r = p.map ((Prod.snd ∘ Prod.fst)) ++ j2r'.map Prod.fst ++ j1l') ∧
  (j2r = p.map Prod.snd ++ j2r'.map Prod.snd ++ j1r')


-- TODO: Can I write differently the lambda that extract the element from p's queue
def φ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  (ψ rhs lhs) ∧ (partially_flushed lhs)

-- loogle.lean-lang.org
theorem φ_indistinguishable :
  ∀ x y, φ x y → Module.indistinguishable (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) x y := by
  intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ Hφ
  constructor <;> intro ident ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ v H
  . by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . unfold rhsModule lhsModule at *; simp at v H HContains; simp
      rcases HContains with h | h | h
      all_goals
        subst ident
        rw [PortMap.rw_rule_execution] at *
        apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
        rw [PortMap.rw_rule_execution]
        unfold φ ψ at Hφ <;> simp at Hφ
        dsimp
        and_intros <;> rfl
    . exfalso; exact (PortMap.getIO_not_contained_false H HContains)
  . by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . unfold rhsModule lhsModule at *; simp at v H HContains; simp
      subst ident
      rw [PortMap.rw_rule_execution] at *
      simp at H
      repeat cases ‹_ ∧ _›
      subst_vars
      cases ‹partially_flushed _› <;> simp at *
      . rename_i left
        rw [List.map_eq_cons_iff] at left
        obtain ⟨ ⟨v'1, v'2⟩, j2lr, h1, h2, h3⟩ := left
        subst_vars
        obtain ⟨⟨v111, v112⟩, v12⟩ := v
        dsimp at *
        rename_i left
        rw [List.cons.injEq] at left
        repeat cases left
        subst_vars
        apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
        rw [PortMap.rw_rule_execution]
        dsimp
        and_intros <;> try rfl
      . rename_i left
        rw [List.map_eq_cons_iff] at left
        obtain ⟨ ⟨v'1, v'2⟩, j2lr, h1, h2, h3⟩ := left
        subst_vars
        obtain ⟨⟨v111, v112⟩, v12⟩ := v
        dsimp at *
        rename_i left
        rw [List.cons.injEq] at left
        repeat cases left
        subst_vars
        apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
        rw [PortMap.rw_rule_execution]
        dsimp
        and_intros <;> try rfl
    . exfalso; exact (PortMap.getIO_not_contained_false H HContains)

theorem something':
  ∀ s, ∃ s', existSR (lhsModule T₁ T₂ T₃).internals s s' ∧ partially_flushed s' := by
  intro ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩
  induction l3 generalizing l1 l2 l4 with
  | nil =>
    apply Exists.intro
    and_intros
    . apply existSR_reflexive
    . constructor
  | cons x xs ih =>
    cases l4
    . apply Exists.intro
      and_intros
      . apply existSR_reflexive
      . constructor
    . rename_i head tail
      specialize ih (l1 ++ [(x, head)]) l2 tail
      obtain ⟨ ⟨⟨_, _⟩, ⟨_, _⟩⟩, HExists, HPartiallyFlushed⟩ := ih
      apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
      and_intros
      . apply existSR.step _ ⟨ ⟨ _, _ ⟩, _, _ ⟩ _
        . unfold lhsModule; simp
          rfl
        . repeat apply Exists.intro
          and_intros <;> rfl
        . apply HExists
      . assumption

theorem something:
  ∀ i s s', ψ i s → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i s' := by
  intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ s s' Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold lhsModule at Hrule; simp at Hrule
    subst_vars
    obtain ⟨_, _, _, _, _, _, _, _⟩ := c
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
    rename_i a _ _ _ _ _ b; simp at a b
    obtain ⟨ ⟨_, _⟩, ⟨_, _⟩⟩ := a
    obtain ⟨ ⟨_, _⟩ , ⟨_, _⟩⟩ := b
    unfold ψ at *; simp at *
    subst_vars
    obtain ⟨ _, ⟨_, _⟩ ⟩ := Hψ
    simp; and_intros <;> assumption

theorem something'':
  ∀ i i' s, ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → ψ i' s := by
  intro i i' ⟨⟨_, _⟩, ⟨_, _⟩⟩ Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold rhsModule at Hrule; simp at Hrule
    cases Hrule <;> subst_vars
    . obtain ⟨_, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨_, _⟩, _⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> try simp
      . assumption
      . rename_i synth1 _ _ _ _ _ _
        rw [<- synth1]; subst_vars
        assumption
      . assumption
    . obtain ⟨_, _, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> simp
      . assumption
      . assumption

theorem s' {T₁ T₂ T₃: Type _} (i i': rhsModuleType T₁ T₂ T₃) :
  ∀ rule, rule ∈ (rhsModule T₁ T₂ T₃).internals ∧ rule i i' → existSR (rhsModule T₁ T₂ T₃).internals i i' := by
    intro rule ⟨_, _⟩
    apply existSR.step i i' i' rule
    . assumption
    . assumption
    . exact existSR_reflexive

theorem lengthify {T₁: Type _} (a b: List T₁): a = b → a.length = b.length := by
  intro heq; rw [heq]

theorem takify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.take l l₁ = List.take l l₂ := by
  intro heq; rw [heq]

theorem dropify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.drop l l₁ = List.drop l l₂ := by
  intro heq; rw [heq]

theorem product_is_list_zip {T₁ T₂: Type _} (x: List (T₁ × T₂)): x = List.zip (List.map Prod.fst x) (List.map Prod.snd x) := by
  induction x with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.zip_cons_cons, <- ih]

theorem append_iff {α} {a b c d : List α} : a.length = c.length → (a ++ b = c ++ d ↔ a = c ∧ b = d) := by
  intro lengths
  constructor
  . intro h
    and_intros
    . replace h := congrArg (List.take a.length) h
      rw [List.take_left, lengths, List.take_left] at h
      assumption
    . apply dropify a.length at h
      rw [List.drop_left, lengths, List.drop_left] at h
      assumption
  . intro ⟨_, _⟩; subst_vars; rfl

-- example {T1 T2 T3} : ∀ s : lhsModuleType T1 T2 T3, (∀ r s', r ∈ (lhsModule T1 T2 T3).internals → ¬ r s s') →
example {T1 T2 T3} : ∀ s : lhsModuleType T1 T2 T3, (¬ ∃ s' r, r ∈ (lhsModule T1 T2 T3).internals ∧ r s s') → (∀ r ∈ (lhsModule T1 T2 T3).internals, ∀ s', ¬ r s s') := by
  intro s H r hr s' hrss
  apply H
  exists s', r

example {T1 T2 T3} : ∀ s : lhsModuleType T1 T2 T3, (∀ r ∈ (lhsModule T1 T2 T3).internals, ∀ s', ¬ r s s') → partially_flushed s := by
  intro ⟨s1, s2, s3⟩ hr; dsimp [lhsModuleType, lhsModule] at *
  specialize hr _ (by simp; rfl)
  cases s2 <;> cases s3 <;> try constructor
  exfalso
  apply hr ⟨⟨_, _⟩, ⟨_, _⟩⟩
  iterate 6 (apply Exists.intro _)
  and_intros <;> dsimp

-- lhsModule is spec is trivial, because you just do the same steps as lhsModule'
-- lhsModule' being spec is not trivial
-- rhsModule' ⊑ lshModule' could be interesting, not sure if easier.
def lhsModule' : StringModule (lhsModuleType T₁ T₂ T₃) :=
  {
    inputs := (lhsModule T₁ T₂ T₃).inputs.mapVal (λ k v =>
        ⟨v.1, fun s ret s'' =>
          ∃ (s' : lhsModuleType T₁ T₂ T₃), v.2 s ret s'
            ∧ existSR (lhsModule T₁ T₂ T₃).internals s' s''                -- Allow rule executions
            ∧ (∀ r ∈ (lhsModule T₁ T₂ T₃).internals, ∀ s_n, ¬ r s'' s_n)⟩  -- Ensure they are terminal
      ),
    outputs := (lhsModule T₁ T₂ T₃).outputs,
    init_state := fun _ => True,
  }

inductive empty_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ q₁ q₂ q₃, empty_internal ⟨⟨[], q₃⟩, ⟨q₁, q₂⟩⟩

inductive single_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ v q₁ q₂ q₃, single_internal ⟨⟨[v], q₃⟩, ⟨q₁, q₂⟩⟩

theorem existSR_single_step {S : Type _} {rules : List (S → S → Prop)}:
  ∀ s s' rule, rule ∈ rules ∧ rule s s' → existSR rules s s' := by
    intro s s' rule ⟨_, _⟩
    apply existSR.step s s' s' rule
    . assumption
    . assumption
    . exact existSR_reflexive

theorem existSR_single_step' {S : Type _} (rules : List (S → S → Prop)):
  ∀ s s', ∀ rule ∈ rules, rule s s' → existSR rules s s' := by
    intros
    apply existSR_single_step <;> and_intros <;> assumption

theorem b:
  ∀ s, ∃ s', existSR (lhsModule T₁ T₂ T₃).internals s s' :=
by
  intro s; use s; apply existSR_reflexive

theorem f: ∀ ident,
  ((rhsModule T₁ T₂ T₃).outputs.getIO ident).fst = ((lhsModule T₁ T₂ T₃).outputs.getIO ident).fst :=
by
  sorry

def ψ₂ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) :=
  ψ rhs lhs ∧ empty_internal lhs

-- TODO: maybe we can make the proof better?
theorem f₁: ∀ ident i₁ i₂ v s₁, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  ψ₂ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → ∃ s₂, rule s₁ s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ v ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- Fetch the output rule
    simp [rhsModule] at HContains; subst HContains
    obtain ⟨hψ, h₂⟩ := h₂
    cases h₂
    dsimp [ψ] at hψ
    obtain ⟨_, _, _⟩ := hψ
    subst_vars
    -- work on h₃
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    repeat
      cases ‹_ ∧ _›
    subst_vars
    -- work on h₁
    simp [lhsModule] at h₁; subst h₁
    dsimp
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    repeat
      apply Exists.intro
    simp
    and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem f': ∀ s₁ s₂, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  empty_internal s₁
  → rule s₁ s₂
  → single_internal s₂ :=
by
  intro ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  simp [lhsModule] at h₁
  subst h₁

  cases h₂
  dsimp at h₃
  simp at h₃
  obtain ⟨_, _, _, _, _, _, _⟩ := h₃
  repeat
    cases ‹_ ∧ _›
  subst_vars
  rw [List.nil_append]
  constructor

theorem f'': ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → single_internal s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ((f ident).mp v) s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ ⟨⟨_, _⟩,⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₃; rw [PortMap.rw_rule_execution] at h₃; simp at h₃
    cases h₂
    dsimp [ψ] at h₁
    repeat
      cases ‹_ ∧ _›
    subst_vars

    unfold lhsModule
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    rw [PortMap.rw_rule_execution]; dsimp
    and_intros
    . sorry -- TODO: TRIVIAL, BUT ANNOYING TO WRITE
    . rfl
    . rfl
    sorry -- TODO: REMOVE THIS, ONLY HERE TO SATISFY THE GOAL OF THE TYPE FOR EXISTANTIALS
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem f₃: ∀ ident s₁ s₂ v,
  single_internal s₁
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → empty_internal s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- fetch the single output port ident
    simp [lhsModule] at HContains; subst HContains
    unfold lhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂
    dsimp at h₂
    simp at h₂
    repeat
      cases ‹_ ∧ _›
    subst_vars
    cases h₁
    constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem f₄: ∀ ident i₁ i₂ v s₁ s₂,
  ψ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ((f ident).mp v) s₂
  → ψ i₂ s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂; simp at h₂
    simp at *
    repeat
      cases ‹_ ∧ _›
    simp at *
    cases ‹_ ∧ _›
    subst_vars

    dsimp [ψ]
    and_intros
    . simp at *; assumption
    . simp at *; assumption
    . simp at *; assumption
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

theorem refines {T: Type _} [DecidableEq T]: rhsModule T₁ T₂ T₃ ⊑_{ψ₂} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hψ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i

      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h | h | h <;> subst_vars <;> simp
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp -- TODO: Remove this simp here
        . -- verify that the invariant holds when we flush the system
          use ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [ψ₂, ψ] at Hψ
            obtain ⟨⟨h, _, _⟩, hₑ⟩ := Hψ
            dsimp [ψ₂, ψ]
            and_intros
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . assumption
            . assumption
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [heq.mp s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [heq.mp s]⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [ψ₂, ψ] at Hψ
            obtain ⟨⟨_, h, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [ψ₂, ψ]
            and_intros
            . assumption
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . rfl
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, sj1l, sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [ψ₂, ψ] at Hψ
            obtain ⟨⟨_, _, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [ψ₂, ψ]
            and_intros
            . assumption
            . assumption
            . rw [<- List.append_assoc]
            . cases hₑ; constructor
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . have: ∃ rule, rule ∈ (lhsModule T₁ T₂ T₃).internals := by
        simp [lhsModule]
      obtain ⟨rule, h⟩ := this
      have: ∃ almost_mid_s, rule init_s almost_mid_s := by
        apply (f₁ _ init_i i) at Hψ
        . specialize Hψ hrule
          assumption
        . assumption
      obtain ⟨almost_mid_s, _⟩ := this
      use almost_mid_s
      rw [exists_and_left]
      and_intros
      . apply existSR_single_step' <;> assumption
      . unfold ψ₂ at Hψ
        obtain ⟨_, _⟩ := Hψ
        have hₛ: single_internal almost_mid_s := by
          apply f' <;> assumption
        have: existSR (lhsModule T₁ T₂ T₃).internals init_s almost_mid_s := by
          apply existSR_single_step' <;> assumption
        have hψ: ψ init_i almost_mid_s := by
          apply something <;> assumption
        clear this
        have: ∃ mid_s, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd almost_mid_s ((f ident).mp v) mid_s := by
          apply f'' <;> assumption
        obtain ⟨mid_s, _⟩ := this
        use mid_s
        apply And.intro
        . assumption
        . unfold ψ₂
          apply And.intro
          . apply f₄ <;> assumption
          . apply f₃ <;> assumption
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . dsimp [ψ₂] at *
      obtain ⟨_, _⟩ := Hψ
      . apply And.intro
        . apply (something'' init_i)
          . assumption
          . apply existSR_single_step' <;> assumption
        . assumption

end DataflowRewriter.JoinRewrite
