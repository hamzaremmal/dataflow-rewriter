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

---------------------------------------------------------------------------------------------------
------
---------------------------------------------------------------------------------------------------

inductive partially_flushed: lhsModuleType T₁ T₂ T₃ -> Prop where
| lhs: ∀ lower arb, partially_flushed ⟨lower, [], arb⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, arb, []⟩

def ψ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  let ⟨⟨j2l, j2r⟩, ⟨j1l, j1r⟩⟩ := lhs
  let ⟨⟨j2l', j2r'⟩, ⟨⟨j1l', j1r'⟩, p⟩⟩ := rhs
  (j2l.map Prod.fst ++ j1l = p.map (Prod.fst ∘ Prod.fst) ++ j2l') ∧
  (j2l.map Prod.snd ++ j1r = p.map ((Prod.snd ∘ Prod.fst)) ++ j2r'.map Prod.fst ++ j1l') ∧
  (j2r = p.map Prod.snd ++ j2r'.map Prod.snd ++ j1r')

def φ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  (ψ rhs lhs) ∧ (partially_flushed lhs)

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

theorem lengthify {T₁: Type _} (a b: List T₁): a = b → a.length = b.length := by
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
    . replace h := congrArg (List.drop a.length) h
      rw [List.drop_left, lengths, List.drop_left] at h
      assumption
  . intro ⟨_, _⟩; subst_vars; rfl

----------------------------------------------------------------------------------------------
------------------------------ PROOF THAT rhsModule REFINES lhsModule -----------------------------
---------------------------------------------------------------------------------------------------

theorem refines: rhsModule T₁ T₂ T₃ ⊑_{φ} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i
      unfold rhsModule at HContains; simp at HContains

      rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution] at a <;> simp at a
      . obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := .top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp
        . -- verify that the invariant holds when we flush the system
          obtain ⟨s', ⟨_, _⟩⟩ := something' ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩ -- We flush the system to reach s'
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something _ (⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . simp only [<- List.append_assoc, List.append_left_inj]
                  assumption
                . assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := something' ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something _ (⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
                  assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r ++ [s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := something' ⟨⟨sj2l, sj2r ++ [s]⟩, sj1l, sj1r⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something _ (⟨sj2l, sj2r  ++ [s]⟩, sj1l, sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
              . assumption
            . assumption
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    · obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨ij2l, ij2r⟩, ⟨ij1l, ij1r⟩, ip⟩ := init_i
      obtain ⟨⟨ij2l', ij2r'⟩, ⟨ij1l', ij1r'⟩, ip'⟩ := i
      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h <;> subst_vars
      <;> simp <;>
      rw [PortMap.rw_rule_execution (by simp [PortMap.getIO]; rfl)] at hrule <;>
      simp at hrule
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := hrule
      repeat cases ‹_∧_›
      subst_vars
      rename_i hlval hrval hpf
      dsimp at *
      rename_i htmp; cases htmp
      cases hpf
      · simp at hlval; simp at *
        rw [<- List.take_append_drop ij2l.length (List.map Prod.fst ij2r ++ ij1l)] at hrval
        --rw [<- List.append_assoc (List.map (Prod.snd ∘ Prod.fst) ip')] at hrval
        --rw [<- List.append.eq_2 _ _ ((List.map (Prod.snd ∘ Prod.fst) ip' ++ List.take ij2l.length (List.map Prod.fst ij2r' ++ ij1l'))] at hrval
        rw [show v.1.2 ::
            (List.map (Prod.snd ∘ Prod.fst) ip' ++
              (List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l) ++
                List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l))) = v.1.2 ::
            (List.map (Prod.snd ∘ Prod.fst) ip' ++
              List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l)) ++
                List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l) by simp] at hrval
        rw [append_iff] at hrval
        obtain ⟨hrvall, _⟩ := hrval
        . subst_vars
          apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
          and_intros <;> dsimp
          · rewrite [product_is_list_zip sj2l, hlval, hrvall]; rfl
          · apply lengthify at hlval; simp at hlval
            apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
            rw [List.append_nil, <- List.zip_eq_zipWith, List.map_fst_zip]
            simp [hrvall] -- lia + assumption in context
          · apply lengthify at hlval; simp at hlval
            apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
            rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
            . simp only [List.append_assoc, List.take_append_drop]
            . simp only [List.length_append, List.length_map, List.length_take, add_le_add_iff_left, inf_le_left]
          · rewrite [List.append_assoc]; rfl
          · constructor
        . apply lengthify at hlval; simp at hlval
          apply lengthify at hrval; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrval
          simp only [hlval, List.length_map, List.length_cons, List.length_append, List.length_take,
            add_left_inj, add_right_inj, left_eq_inf] -- lengthify the goal
          simp only [le_iff_exists_add, <- hrval, add_right_inj, exists_eq'] -- lia
      . simp at hrval; simp at *
        rw [<- List.take_append_drop (ij2r.length + ij1l.length) ij2l] at hlval
        rw [show v.1.1 ::
            (List.map (Prod.fst ∘ Prod.fst) ip' ++
              (List.take (ij2r.length + ij1l.length) ij2l ++
                List.drop (ij2r.length + ij1l.length) ij2l)) = v.1.1 ::
            (List.map (Prod.fst ∘ Prod.fst) ip' ++
              List.take (ij2r.length + ij1l.length) ij2l) ++
                List.drop (ij2r.length + ij1l.length) ij2l by simp] at hlval
        rw [append_iff] at hlval
        obtain ⟨hlvall, hlvalr⟩ := hlval
        . subst_vars
          apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
          . and_intros <;> dsimp
            . rewrite [product_is_list_zip sj2l, hrval, hlvall]; rfl
            . apply lengthify at hrval; simp at hrval
              apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
              simp [<- List.zip_eq_zipWith, List.map_fst_zip, hlvall]
            . apply lengthify at hrval; simp at hrval
              apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
              rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
              . simp
              . simp [hlvall]
            . simp
            . constructor
        . apply lengthify at hrval; simp [add_comm _ 1, add_right_inj, add_assoc] at hrval
          apply lengthify at hlval; simp [hrval, add_comm _ 1, add_left_inj, add_assoc] at hlval
          simp only [hrval, List.length_map, List.length_cons, add_comm _ 1, add_right_inj, List.length_append, List.length_take, left_eq_inf] -- lengthify the goal
          simp only [le_iff_exists_add, <- hlval, add_right_inj, exists_eq', add_assoc] -- lia
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros rule mid_i _ _
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . unfold φ at *
      obtain ⟨_, _⟩ := Hφ
      apply And.intro
      . apply (something'' init_i)
        . assumption
        . apply existSR_single_step <;> and_intros <;> assumption
      . assumption

---------------------------------------------------------------------------------------------------
--------------------------------- MORE GLOBAL LEMMAS AND THEOREMS ---------------------------------
---------------------------------------------------------------------------------------------------

-- TODO: Move this theorem into a more general file
theorem AssocList.mapVal_mapVal {K V₁ V₂ V₃ : Type _} (m : AssocList K V₁) {f : K → V₂ → V₃} {g : K → V₁ → V₂} :
  AssocList.mapVal f (AssocList.mapVal g m) = AssocList.mapVal (fun k v => f k (g k v)) m := by
  induction m with
  | nil => rfl
  | cons _ _ _ ih => dsimp; rw [ih]

---------------------------------------------------------------------------------------------------
---------------------------------- DEFINITION OF A FLUSHED MODULE ---------------------------------
---------------------------------------------------------------------------------------------------

def pf {S: Type _} (rules: List (S → S → Prop)) (s: S) :=
  ∀ r ∈ rules, ∀ s', ¬ r s s'

---------------------------------------------------------------------------------------------------
----
---------------------------------------------------------------------------------------------------

-- example {T1 T2 T3} : ∀ s : lhsModuleType T1 T2 T3, (∀ r s', r ∈ (lhsModule T1 T2 T3).internals → ¬ r s s') →
example {T1 T2 T3} : ∀ s : lhsModuleType T1 T2 T3, (¬ ∃ s' r, r ∈ (lhsModule T1 T2 T3).internals ∧ r s s') → (∀ r ∈ (lhsModule T1 T2 T3).internals, ∀ s', ¬ r s s') := by
  intro s H r hr s' hrss
  apply H
  exists s', r

theorem pf_is_partially_flushed : ∀ (s : (lhsModuleType T₁ T₂ T₃)), pf (lhsModule T₁ T₂ T₃).internals s → partially_flushed s := by
  intro ⟨s1, s2, s3⟩ hr; dsimp [lhsModuleType, lhsModule] at *
  specialize hr ?r (by simp; rfl)
  cases s2 <;> cases s3 <;> try constructor
  exfalso
  apply hr ⟨⟨_, _⟩, ⟨_, _⟩⟩
  iterate 6 (apply Exists.intro _)
  and_intros <;> dsimp

theorem partially_flushed_is_pf : ∀ (s : (lhsModuleType T₁ T₂ T₃)), partially_flushed s → pf (lhsModule T₁ T₂ T₃).internals s := by
  intro s h
  cases h
  all_goals
    unfold pf
    intros rule hᵣ _ h
    simp [lhsModule] at hᵣ <;> subst hᵣ
    simp at h

---------------------------------------------------------------------------------------------------
-----
---------------------------------------------------------------------------------------------------

--structure Flushed (S : Type _) where
--  val : S

--instance {S: Type _} : Coe (Flushed S) S where
--  coe := Flushed.val

-- Build a Module that always flushes from a given Module
def flushed {Ident S : Type _} (mod: Module Ident S): Module Ident S :=
  {
    inputs := mod.inputs.mapVal (λ _ v =>
        ⟨v.1, λ s ret s'' =>
          ∃ s', v.2 s ret s'
            ∧ existSR mod.internals s' s'' -- Allow to execute the rules
            ∧ pf mod.internals s''⟩        -- Ensure we reach a flushed state
      ),
    outputs    := mod.outputs,
    init_state := λ s =>
      ∃ s', mod.init_state s
          ∧ existSR mod.internals s s'     -- Allow to execute the rules
          ∧ pf mod.internals s'            -- Ensure we reach a flushed state
  }

theorem flushed_preserves_input_types {Ident S : Type _} (mod: Module Ident S):
  (flushed mod).inputs.mapVal (λ _ v => Sigma.fst v) = mod.inputs.mapVal (λ _ v => Sigma.fst v) :=
by
  rw [flushed, AssocList.mapVal_mapVal]

theorem flushed_preserves_outputs {Ident S : Type _} (mod: Module Ident S): (flushed mod).outputs = mod.outputs := by
  rfl
---------------------------------------------------------------------------------------------------
----
---------------------------------------------------------------------------------------------------

-- TODO: Can I add attributes to use them directly without affecting the proofs
def flhsModule (T₁ T₂ T₃ : Type) := flushed (lhsModule T₁ T₂ T₃)
def frhsModule (T₁ T₂ T₃ : Type) := flushed (rhsModule T₁ T₂ T₃)

variable (T₁ T₂ T₃) in
def_module flushed_lhsModuleType : Module String (lhsModuleType T₁ T₂ T₃) :=
  flushed (lhsModule T₁ T₂ T₃)
reduction_by
  dsimp [flushed]
  conv =>
    pattern (occs := *) (Module.inputs _)
    all_goals unfold lhsModule
  conv =>
    pattern (occs := *) (Module.outputs _)
    all_goals unfold lhsModule
  dsimp

---------------------------------------------------------------------------------------------------
---
---------------------------------------------------------------------------------------------------

instance {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S) : MatchInterface (flushed mod) mod := by
  rw [MatchInterface_simpler_iff]
  rw [flushed_preserves_input_types, flushed_preserves_outputs]
  intros <;> and_intros <;> rfl

instance {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S) : MatchInterface mod (flushed mod) := by
  haveI: MatchInterface (flushed mod) mod := by infer_instance
  apply MatchInterface_symmetric <;> assumption

instance {Ident S₁ S₂: Type _} [DecidableEq Ident] (mod₁: Module Ident S₁) (mod₂: Module Ident S₂) [MatchInterface mod₁ mod₂]: MatchInterface (flushed mod₁) (flushed mod₂) := by
  have: MatchInterface (flushed mod₁) mod₁ := by infer_instance
  have: MatchInterface mod₂ (flushed mod₂) := by infer_instance
  have: MatchInterface mod₁ (flushed mod₂) := by
    apply MatchInterface_transitive <;> assumption
  apply MatchInterface_transitive <;> assumption

---------------------------------------------------------------------------------------------------
------------------------- PROOF THAT A FLUSHED VERSION REFINES THE MODULE -------------------------
---------------------------------------------------------------------------------------------------

theorem internal_rules_deterministic:
  ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ s₁ s₂ s₃, rule s₁ s₂ → rule s₁ s₃ → s₂ = s₃ :=
by
  intro _ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  simp [lhsModule] at *
  subst_vars
  dsimp at h₁ h₂
  obtain ⟨_, _, _, _, _, _, _⟩ := h₁
  obtain ⟨_, _, _, _, _, _, _⟩ := h₂
  repeat
    cases ‹_ ∧ _›
    try simp at *
    try subst_vars
  rfl

theorem output_rules_deterministic: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₃
  → s₂ = s₃ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains; subst HContains
    dsimp [lhsModule] at h₁ h₂
    rw [PortMap.rw_rule_execution] at h₁ h₂
    dsimp at h₁ h₂
    repeat
      cases ‹_ ∧ _›
      try simp at *
      try subst_vars
    rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem input_rules_deterministic: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₃
  → s₂ = s₃ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
  . simp [lhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    all_goals
      dsimp [lhsModule] at h₁ h₂
      rw [PortMap.rw_rule_execution] at h₁ h₂
      dsimp at h₁ h₂
      repeat
        cases ‹_ ∧ _›
        try simp at *
        try subst_vars
      rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

-- TODO: Rename this theorem
theorem bll {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S):
  ∀ ident, ((flushed mod).inputs.getIO ident).fst = (mod.inputs.getIO ident).fst :=
by
  intro ident
  -- why can't I just write one or use repeat
  unfold PortMap.getIO
  rw [<- Option.getD_map Sigma.fst, <- Option.getD_map Sigma.fst]
  rw [Batteries.AssocList.find?_map_comm, Batteries.AssocList.find?_map_comm]
  rw [flushed_preserves_input_types]

theorem bll₂ {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S):
  ∀ ident, (mod.inputs.getIO ident).fst = ((flushed mod).inputs.getIO ident).fst :=
by
  intro; symm; apply bll

theorem contains_of_cons_ne_head {K V : Type _} [DecidableEq K] {k k' : K} {v : V} : ∀ tl,
  Batteries.AssocList.contains k (Batteries.AssocList.cons k' v tl) = true
  → k' ≠ k
  → Batteries.AssocList.contains k tl = true :=
by
  intros _ h _
  simp at *
  cases h
  . exfalso; contradiction
  . assumption

universe u
theorem portmap_mapVal {S: Type _} {Ident: Type _} [DecidableEq Ident] {f: (Σ T : Type u, (S → T → S → Prop)) → (Σ T : Type u, (S → T → S → Prop))} (ports: PortMap Ident (Σ T : Type u, (S → T → S → Prop))):
  ∀ ident, ports.contains ident
  → PortMap.getIO (ports.mapVal (λ _ v => f v)) ident = f (PortMap.getIO ports ident) :=
by
  intros ident h
  induction ports with
  | nil =>
    exfalso; contradiction
  | cons key _ tail ih =>
    rw [Batteries.AssocList.mapVal_cons]
    by_cases key = ident
    . subst_vars
      dsimp [PortMap.getIO]
      repeat rw [Batteries.AssocList.find?_cons_eq]
      rfl
    . dsimp [PortMap.getIO]
      dsimp [PortMap.getIO] at ih
      rw [Batteries.AssocList.find?_cons_neq] <;> try assumption
      rw [Batteries.AssocList.find?_cons_neq] <;> try assumption
      apply ih <;> try dsimp <;> assumption
      apply contains_of_cons_ne_head <;> assumption

def f {Ident S: Type _} (v: (Σ T: Type u, (S → T → S → Prop))) (mod: Module Ident S) : (Σ T: Type _, (S → T → S → Prop)):=
  ⟨v.fst, fun s ret s'' => ∃ s', v.snd s ret s' ∧ existSR mod.internals s' s'' ∧ pf mod.internals s''⟩

theorem f_preserve_fst {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S)(ident: InternalPort Ident) :
  ((flushed mod).inputs.getIO ident).fst = (f (mod.inputs.getIO ident) mod).fst :=
by
  dsimp [f, flushed]
  induction mod.inputs with
  | nil => dsimp
  | cons  key hd tl ih =>
    rw [Batteries.AssocList.mapVal]
    by_cases key = ident
    . subst_vars
      repeat rw [PortMap.getIO_cons]
    . rw [PortMap.getIO_cons', ih, PortMap.getIO_cons'] <;> assumption

theorem bll' {Ident S: Type _} [DecidableEq Ident]:
  ∀ (mod: Module Ident S) ident s v s',
    ((flushed mod).inputs.getIO ident).snd s v s'
      -> ∃ s'', (mod.inputs.getIO ident).snd s ((bll mod ident).mp v) s'' ∧ existSR (mod.internals) s'' s' ∧ pf mod.internals s':=
by
  intros mod ident s₁ v s₂ h
  dsimp [flushed] at h
  simp [flushed] at *

  have h₁: (PortMap.getIO (mod.inputs.mapVal (fun _ v => f v mod)) ident = f (PortMap.getIO mod.inputs ident) mod) := by
    apply portmap_mapVal
    sorry -- TODO: annoying but trivial

  have: (PortMap.getIO (mod.inputs.mapVal (λ _ v => f v mod)) ident) = ((PortMap.getIO
      (Batteries.AssocList.mapVal
        (fun x v =>
          ⟨v.fst, fun s ret s'' => ∃ s', v.snd s ret s' ∧ existSR mod.internals s' s'' ∧ pf mod.internals s''⟩)
        mod.inputs)
      ident)) := by
      unfold f
      rfl
  rw [this] at h₁; clear this
  have: (f (mod.inputs.getIO ident) mod).snd s₁ ((f_preserve_fst mod ident).mp v) s₂ := by
    sorry
  clear h₁ h
  unfold f at this
  dsimp [f] at this
  assumption

-- TODO: Prove the following lemmas
--   - if a rule can be applied, the port is in the portmap
--   - if a port is in the portmap, the same port is in the portmap of flushed
--   - if I have a port in the portmap, then for any state, I can apply the rule linked to that port
theorem abc: ∀ ident s₁ v s₂,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s₁ ((bll₂ (lhsModule T₁ T₂ T₃) ident).mp v) s₃ :=
by
  intros
  sorry

theorem abc₂: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s₁ ((bll₂ (lhsModule T₁ T₂ T₃) ident).mp v) s₃
  → pf (lhsModule T₁ T₂ T₃).internals s₃ :=
by
  intros _ _ _ _ _ _ h
  apply bll' at h
  obtain ⟨s, _, _, _⟩ := h
  assumption

theorem abc₃: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s₁ ((bll₂ (lhsModule T₁ T₂ T₃) ident).mp v) s₃
  → existSR (lhsModule T₁ T₂ T₃).internals s₂ s₃ :=
by
  intros _ s₁ _ s₂ s₃ _ h
  apply bll' at h
  obtain ⟨s, _, _, _⟩ := h
  simp at *
  have: s = s₂ := by apply input_rules_deterministic <;> assumption
  subst this
  assumption

theorem bll'₂: ∀ ident s v s',
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s v s'
  -> ∃ s'', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s ((bll₂ (lhsModule T₁ T₂ T₃) ident).mp v) s'' ∧ existSR ((lhsModule T₁ T₂ T₃).internals) s' s'' ∧ pf (lhsModule T₁ T₂ T₃).internals s'' :=
by
  intros ident s v _ _
  have: ∃ s'', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s ((bll₂ (lhsModule T₁ T₂ T₃) ident).mp v) s'' := by
    apply abc <;> assumption
  obtain ⟨s₁, h⟩ := this
  use s₁
  and_intros <;> try assumption
  . apply abc₃ <;> assumption
  . apply abc₂ <;> assumption


theorem φ₁_indistinguishable' {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S):
  ∀ x y, x = y → Module.indistinguishable (flushed mod) mod x y :=
by
  intro _ _ h
  subst_vars
  constructor
  . intro _ _ _ h
    apply bll' at h
    obtain ⟨s, _, _⟩ := h
    use s
  . intro _ new_i _ _
    dsimp [flushed] at *
    use new_i

theorem refines₀ {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S): flushed mod ⊑_{Eq} mod := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  --unfold φ₁ at Hφ;
  subst_vars
  apply Module.comp_refines.mk
  -- input rules
  . intro _ mid_i v h
    apply bll' at h
    obtain ⟨s', _, _, _⟩ := h
    use s', mid_i
  -- output rules
  . intro _ mid_i _ _
    use mid_i
    and_intros
    . simp only [flushed, eq_mp_eq_cast, cast_eq] at *
      assumption
    . rfl
  -- internal rules
  . intro _ mid_i _ _
    use mid_i
    and_intros
    . apply existSR.step
      . simp only [flushed, List.not_mem_nil] at *
      . assumption
      . apply existSR_reflexive
    . rfl

---------------------------------------------------------------------------------------------------
------------------------- PROOF THAT A MODULE REFINES THE FLUSHED VERSION -------------------------
---------------------------------------------------------------------------------------------------

def φ₂ {S: Type _} (rules: List (S → S → Prop))(lhs : S) (rhs : S) : Prop :=
  -- By using the internal rules of the non-flushed version, we should reach the flushed one
  existSR rules lhs rhs ∧ pf rules rhs

theorem refines₀' {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S): mod ⊑_{φ₂ mod.internals} flushed mod := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  sorry

theorem bla {α : Type _} {a c : α} (b : List α) :
  a ∈ b → c ∈ b → b.length = 1 → a = c :=
by
  intro ha hc hl
  cases b with
  | nil => exfalso; rw [List.length_nil] at hl; contradiction
  | cons x xs => cases xs with
    | nil =>
      simp at *; subst_vars; rfl
    | cons x' xs' =>
      repeat rw [List.length_cons] at hl
      rw [Nat.add_eq_right] at hl
      rw [Nat.add_eq_zero] at hl
      cases ‹ _ ∧ _ ›
      contradiction

theorem hamza₂: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₃ v s₄ :=
by
  intro rule _ ident _ _ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _
  by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
  . -- TODO: Extract it as it's own theorem
    simp [lhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    all_goals
      apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩
      dsimp [lhsModule]
      rw [PortMap.rw_rule_execution]
      simp <;> and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b': ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → rule s₁ s₃
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄ :=
by
  intro rule hᵣ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ v ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains
    simp [lhsModule] at hᵣ
    unfold lhsModule at h₁
    rw [PortMap.rw_rule_execution] at h₁
    subst_vars
    dsimp at *
    obtain ⟨_, _, _, _, _, _, ⟨⟨_ , _⟩ , _⟩, ⟨_ , _⟩, _⟩ := h₂
    simp at *; subst_vars
    repeat cases ‹_ ∧ _›
    subst_vars; simp
    -- extract this as it's own lemma
    apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    dsimp <;> and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)

theorem b'₃: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → rule s₁ s₃
  → ∃ s₄, rule s₂ s₄ :=
by
  intro rule h₁ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₃ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains; subst HContains
    unfold lhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    dsimp at h₃
    simp [lhsModule] at h₁; subst h₁
    obtain ⟨_, _, _, _, _, _, ⟨⟨_ , _⟩ , _⟩, ⟨_ , _⟩, _⟩ := h₂
    simp at *; subst_vars
    repeat cases ‹ _ ∧ _ ›
    subst_vars; simp
    apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩; and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b'₂: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃ s₄,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄
  → rule s₁ s₃
  → rule s₂ s₄ :=
by
  intro rule h₁ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₂ h₃ h₄
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- process and unfold the fact that use the internal rule
    simp [lhsModule] at h₁; subst h₁; dsimp at h₄; dsimp
    -- process the fact we use the output rule
    simp [lhsModule] at HContains; subst HContains
    dsimp [lhsModule] at h₂
    rw [PortMap.rw_rule_execution] at h₂
    dsimp at h₂
    dsimp [lhsModule] at h₃
    rw [PortMap.rw_rule_execution] at h₃
    dsimp at h₃
    obtain ⟨_, _, _, _, _, _, _⟩ := h₄
    repeat
      cases ‹_ ∧ _›
      try simp at *
      try subst_vars
    simp
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b'₅: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃ s₄,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₃ v s₄
  → rule s₁ s₃
  → rule s₂ s₄ :=
by
  intro rule hᵣ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ hᵢ hᵢ' hᵣ'
  by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
  . -- extract the names of the ports
    simp [lhsModule] at HContains
    -- work on the internal rules
    simp [lhsModule] at hᵣ <;> subst hᵣ
    obtain ⟨_, _, _, _, _, _, ⟨⟨_ , _⟩ , _⟩, ⟨_ , _⟩, _⟩ := hᵣ'
    simp at * <;> (repeat cases ‹_ ∧ _›) <;> subst_vars
    -- work on each input rule
    rcases HContains with h | h | h <;> subst h
    all_goals
      dsimp [lhsModule] at hᵢ hᵢ'
      rw [PortMap.rw_rule_execution] at hᵢ hᵢ'
      dsimp at hᵢ hᵢ'
      obtain ⟨⟨_ , _⟩, _, _⟩ := hᵢ
      obtain ⟨⟨_ , _⟩, _, _⟩ := hᵢ'
      subst_vars
      simp
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b'₄: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃ s₄,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → rule s₁ s₃
  → rule s₂ s₄
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄ :=
by
  intro rule h₁ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₂ h₃ h₄
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- process and unfold the fact that use the internal rule
    simp [lhsModule] at h₁; subst h₁; dsimp at h₃ h₄
    -- process the fact we use the output rule
    simp [lhsModule] at HContains; subst HContains
    dsimp [lhsModule] at h₂
    rw [PortMap.rw_rule_execution] at h₂
    dsimp at h₂
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    dsimp
    obtain ⟨_, _, _, _, _, _, _⟩ := h₃
    obtain ⟨_, _, _, _, _, _, _⟩ := h₄
    repeat
      cases ‹_ ∧ _›
      try simp at *
      try subst_vars
    and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b'': ∀ ident s₁ v s₂ s₃,
  existSR (lhsModule T₁ T₂ T₃).internals s₁ s₃
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄ :=
by
  intros ident s₁ v s₂ s₃ h _
  induction h generalizing s₂ with
  | done => use s₂
  | step init mid final rule _ _ _ ih =>
    have: (∃ s₄, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd mid v s₄) := by
      apply b' <;> assumption
    obtain ⟨s, h⟩ := this
    specialize ih s
    apply ih
    assumption

theorem hamza: ∀ ident s₁ v s₂ s₃,
  existSR (lhsModule T₁ T₂ T₃).internals s₁ s₃
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₃ v s₄ :=
by
  intros ident s₁ v s₂ s₃ h _
  induction h generalizing s₂ with
  | done => use s₂
  | step init mid final rule _ _ _ ih =>
    have: (∃ s₄, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd mid v s₄) := by
      apply hamza₂ <;> assumption
    obtain ⟨s, h⟩ := this
    specialize ih s
    apply ih
    assumption

-- "if we pop an output from a flushed state, the resulting state is also flushed"
theorem b₂: ∀ ident s₁ v s₂,
  pf (lhsModule T₁ T₂ T₃).internals s₁
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  →  pf (lhsModule T₁ T₂ T₃).internals s₂ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ hpf h₁
  apply pf_is_partially_flushed at hpf
  apply partially_flushed_is_pf
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains <;> subst HContains
    dsimp [lhsModule] at h₁
    rw [PortMap.rw_rule_execution] at h₁
    repeat
      cases ‹_ ∧ _›; simp at *
    subst_vars
    cases hpf <;> constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b₃: ∀ ident s₁ v s₂ s₃ s₄,
  existSR (lhsModule T₁ T₂ T₃).internals s₁ s₃
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄
  → existSR (lhsModule T₁ T₂ T₃).internals s₂ s₄:=
by
  intros ident s₁ v s₂ s₃ s₄ h _ _
  induction h generalizing s₂ with
  | done =>
    have: s₂ = s₄ := by
      apply output_rules_deterministic <;> assumption
    subst this
    apply existSR_reflexive
  | step init mid _ rule _ _ _ ih =>
    have: (∃ mid', rule s₂ mid' ∧ existSR (lhsModule T₁ T₂ T₃).internals mid' s₄) := by
      have: (∃ m, rule s₂ m) := by
        apply b'₃ <;> assumption
      obtain ⟨m, _⟩ := this
      use m
      and_intros
      . assumption
      . apply ih
        . apply b'₄ _ _ _ init _ s₂ <;> assumption
        . assumption
    obtain ⟨mid', _, _⟩ := this
    apply existSR_transitive _ _ mid'
    . apply existSR_single_step <;> and_intros <;> assumption
    . assumption

theorem refinesfₗₕₛ: lhsModule T₁ T₂ T₃ ⊑_{φ₂ (lhsModule T₁ T₂ T₃).internals} flushed (lhsModule T₁ T₂ T₃) := by
  unfold Module.refines_φ
  intro init_i init_s ⟨Hφ, hpf⟩
  apply Module.comp_refines.mk <;> unfold φ₂ at *
  -- input rules
  . intro ident mid_i v h
    induction Hφ generalizing mid_i with
    | done =>
      apply bll'₂ at h
      obtain ⟨s, _, _, _⟩ := h
      use s, s
      and_intros <;> try assumption
      apply existSR_reflexive
    | step init mid _ rule _ _ _ ih =>
      specialize ih (by assumption)
      have: ∃ s, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd mid v s := by
        apply hamza <;> try assumption
        apply existSR_single_step <;> and_intros <;> assumption
      obtain ⟨s, _⟩ := this
      specialize ih s (by assumption)
      obtain ⟨s₁, s₂, _, _, _, _⟩ := ih
      use s₁, s₂
      and_intros <;> try assumption
      rename_i a _ _
      dsimp [flushed] at a
      apply existSR_norules at a; subst a
      have: rule mid_i s := by apply b'₅ <;> assumption
      apply (existSR_single_step' (lhsModule T₁ T₂ T₃).internals) at this <;> try assumption
      apply existSR_transitive (lhsModule T₁ T₂ T₃).internals _ s <;> assumption
  -- output rules
  . intro _ mid_i _ h
    dsimp [flushed] at *
    apply b'' at Hφ
    specialize Hφ h
    obtain ⟨mid_s, _⟩ := Hφ
    use mid_s
    and_intros <;> try assumption
    . apply b₃ <;> assumption
    . apply b₂ <;> assumption
  -- internal rules
  . intros rule mid_i HRuleInInternal _
    use init_s
    and_intros
    . apply existSR_reflexive
    . cases Hφ with
      | done =>
        unfold pf at hpf
        specialize hpf rule (by exact HRuleInInternal) mid_i
        contradiction
      | step _ mid _ rule' _ _ _ =>
          have: rule = rule' := by
            apply bla at HRuleInInternal
            specialize HRuleInInternal (by assumption) (by dsimp[lhsModule])
            assumption
          subst this
          have: mid_i = mid := by
            apply internal_rules_deterministic <;> assumption
          subst this <;> assumption
    . assumption

---------------------------------------------------------------------------------------------------
----------------------------- PROOF THAT THE FLUSHED LHS REFINES LHS ------------------------------
---------------------------------------------------------------------------------------------------

set_option maxHeartbeats 0 in -- TODO: Don't change the heartbeat
theorem φ₁_indistinguishable :
  ∀ x y, x = y → Module.indistinguishable (flushed (lhsModule T₁ T₂ T₃)) (lhsModule T₁ T₂ T₃) x y := by
  intro x y Hφ
  subst_vars
  constructor <;> intro ident new_i v H
  . by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
    . -- Extract the input ports from the module
      simp [lhsModule] at HContains
      rcases HContains with _ | _ | _
      all_goals
        subst_vars
        unfold flushed lhsModule at H
        rw [PortMap.rw_rule_execution (by simp []; rfl)] at H
        dsimp at H
        obtain ⟨s', _, _⟩ := H
        use s'
        -- Execute the rule in the goal
        simp [lhsModule, PortMap.rw_rule_execution]
        assumption
    . exfalso; exact (PortMap.getIO_not_contained_false H HContains)
  . use new_i
    simp only [eq_mp_eq_cast, cast_eq]
    simp only [flhsModule, flushed] at H
    exact H

-- FROM THE MORE GENERAL PROOF
theorem φ₁_indistinguishableₗₕₛ'' :
  ∀ x y, x = y → Module.indistinguishable (flushed (lhsModule T₁ T₂ T₃)) (lhsModule T₁ T₂ T₃) x y :=
by
  exact φ₁_indistinguishable' (lhsModule T₁ T₂ T₃)

-- DIRECT PROOF
theorem refinesₗₕₛ: flushed (lhsModule T₁ T₂ T₃) ⊑_{Eq} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  subst_vars
  apply Module.comp_refines.mk
  -- input rules
  . intro ident mid_i v Hrule
    by_cases HContains: (flushed (lhsModule T₁ T₂ T₃)).inputs.contains ident
    . simp [flushed, lhsModule] at HContains
      unfold flushed lhsModule at Hrule
      rcases HContains with _ | _ | _ <;> subst_vars
      all_goals
        dsimp [PortMap.rw_rule_execution] at Hrule
        obtain ⟨s', _, _, _⟩ := Hrule
        use s', mid_i
        apply And.intro
        . unfold flushed lhsModule
          simp [PortMap.rw_rule_execution]
          simp at *
          assumption
        . apply And.intro
          . -- assumption (can I avoid the unfolding inside the existSR that happens earlier)
            unfold lhsModule
            dsimp; assumption
          . rfl
    . exfalso; exact (PortMap.getIO_not_contained_false Hrule HContains)
  -- output rules
  . intro _ mid_i _ _
    use mid_i
    and_intros
    . simp only [flushed, eq_mp_eq_cast, cast_eq] at *
      assumption
    . rfl
  -- internal rules
  . intro _ mid_i _ _
    use mid_i
    and_intros
    . apply existSR.step
      . simp only [flushed, List.not_mem_nil] at *
      . assumption
      . apply existSR_reflexive
    . rfl

-- FROM THE MORE GENERAL PROOF
theorem refinesₗₕₛ': flushed (lhsModule T₁ T₂ T₃) ⊑_{Eq} lhsModule T₁ T₂ T₃ := by
  exact refines₀ (lhsModule T₁ T₂ T₃)

---------------------------------------------------------------------------------------------------
----------------------------- PROOF THAT THE FLUSHED RHS REFINES RHS ------------------------------
---------------------------------------------------------------------------------------------------

-- DIRECT PROOF
set_option maxHeartbeats 0 in
theorem refinesᵣₕₛ: flushed (rhsModule T₁ T₂ T₃) ⊑_{Eq} rhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  subst_vars
  apply Module.comp_refines.mk
  -- input rules
  . intro ident mid_i v Hrule
    by_cases HContains: (flushed (rhsModule T₁ T₂ T₃)).inputs.contains ident
    . simp [flushed, rhsModule] at HContains
      unfold flushed rhsModule at Hrule
      rcases HContains with _ | _ | _ <;> subst_vars
      all_goals
        dsimp [PortMap.rw_rule_execution] at Hrule
        obtain ⟨s', _, _, _⟩ := Hrule
        use s', mid_i
        apply And.intro
        . unfold flushed rhsModule
          simp [PortMap.rw_rule_execution]
          simp at *
          assumption
        . apply And.intro
          . -- assumption (can I avoid the unfolding inside the existSR that happens earlier)
            unfold rhsModule
            dsimp; assumption
          . rfl
    . exfalso; exact (PortMap.getIO_not_contained_false Hrule HContains)
  -- output rules
  . intro _ mid_i _ _
    use mid_i
    and_intros
    . simp only [flushed, eq_mp_eq_cast, cast_eq] at *
      assumption
    . rfl
  -- internal rules
  . intro _ mid_i _ _
    use mid_i
    and_intros
    . apply existSR.step
      . simp only [flushed, List.not_mem_nil] at *
      . assumption
      . apply existSR_reflexive
    . rfl

-- FROM THE MORE GENERAL PROOF
theorem refinesᵣₕₛ': flushed (rhsModule T₁ T₂ T₃) ⊑_{Eq} rhsModule T₁ T₂ T₃ := by
  exact refines₀ (rhsModule T₁ T₂ T₃)

---------------------------------------------------------------------------------------------------
------------------------- PROOF THAT THE FLUSHED RHS REFINES FLUSHED LHS --------------------------
---------------------------------------------------------------------------------------------------

-- TODO: Some of the φ used in this proof can be simplified, specifically when using φ₁
theorem refines₅: flushed (rhsModule T₁ T₂ T₃) ⊑_{λ a b => ∃ c, a = c ∧ (∃ d, φ c d ∧ φ₂ ((lhsModule T₁ T₂ T₃).internals) d b)} flushed (lhsModule T₁ T₂ T₃) := by
  have: flushed (rhsModule T₁ T₂ T₃) ⊑_{Eq}                                (rhsModule T₁ T₂ T₃)         := by
    exact refines₀ (rhsModule T₁ T₂ T₃)
  have: (rhsModule T₁ T₂ T₃)         ⊑_{φ}                                 (lhsModule T₁ T₂ T₃)         := by
    exact refines
  have: (lhsModule T₁ T₂ T₃)         ⊑_{φ₂ (lhsModule T₁ T₂ T₃).internals} flushed (lhsModule T₁ T₂ T₃) := by
    exact refines₀' (lhsModule T₁ T₂ T₃)

  haveI: MatchInterface (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃)) := by
    apply MatchInterface_transitive (lhsModule T₁ T₂ T₃) <;> infer_instance

  have: (rhsModule T₁ T₂ T₃) ⊑_{λ a b => ∃ c, φ a c ∧ φ₂ ((lhsModule T₁ T₂ T₃).internals) c b} flushed (lhsModule T₁ T₂ T₃) := by
    apply Module.refines_φ_transitive _ _ (lhsModule T₁ T₂ T₃) <;> assumption
  apply Module.refines_φ_transitive _ _ (rhsModule T₁ T₂ T₃) <;> assumption

end DataflowRewriter.JoinRewrite
