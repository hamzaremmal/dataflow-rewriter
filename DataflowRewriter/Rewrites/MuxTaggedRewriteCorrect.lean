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
import DataflowRewriter.ExprLow
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Tactic
import DataflowRewriter.Rewrites.MuxTaggedRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace DataflowRewriter.MuxTaggedRewrite

def lhs_int : ExprHigh String := [graph|
    i_t [mod = "io"];
    i_f [mod = "io"];
    i_c [mod = "io"];
    i_tag [mod = "io"];
    o_out [mod = "io"];

    mux [mod = "muxC"];
    join [mod = "joinC"];

    i_t -> mux [inp = "inp0"];
    i_f -> mux [inp = "inp1"];
    i_c -> mux [inp = "inp2"];

    i_tag -> join [inp = "inp0"];

    mux -> join [out = "out0", inp = "inp1"];

    join -> o_out [out = "out0"];
  ]

def lhs_int_extract := lhs_int.extract ["mux", "join"] |>.get rfl

theorem double_check_empty_snd1 : lhs_int_extract.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower_int := lhs_int_extract.fst.lower.get rfl

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Batteries.AssocList.find? Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map

abbrev Ident := Nat

def ε (Tag T : Type _) : IdentMap String (TModule String) :=
  [ ("join", ⟨ _, StringModule.join Tag T ⟩)
  , ("mux", ⟨ _, StringModule.mux T ⟩)
  , ("tagged_mux", ⟨ _, StringModule.mux (Tag × T) ⟩)
  , ("fork", ⟨ _, StringModule.fork Tag 2 ⟩)
  , ("joinC", ⟨ _, StringModule.joinC Tag T Bool ⟩)
  , ("muxC", ⟨ _, StringModule.muxC T ⟩)
  ].toAssocList

def lhsNames := rewrite.input_expr.build_module_names
def lhs_intNames := lhsLower_int.build_module_names
def rhsNames := rewrite.output_expr.build_module_names

def lhsModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| rewrite.input_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]

def lhs_intModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| lhsLower_int, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]

@[drunfold] def lhsModule (Tag T : Type _) : StringModule (lhsModuleType Tag T) := by
  precomputeTac [e| rewrite.input_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''
    dsimp

@[drunfold] def lhs_intModule (Tag T : Type _) : StringModule (lhs_intModuleType Tag T) := by
  precomputeTac [e| lhsLower_int, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''
    dsimp


def rhsModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| rewrite.output_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]

-- #reduce rhsNames
-- #reduce rhsModuleType

@[drunfold] def rhsModule (Tag T : Type _) : StringModule (rhsModuleType Tag T) := by
  precomputeTac [e| rewrite.output_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; arg 2; rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; arg 2; arg 2; rw [Module.connect''_dep_rw]; rfl
    dsimp

attribute [dmod] Batteries.AssocList.find? BEq.beq

instance {Tag T} : MatchInterface (rhsModule Tag T) (lhs_intModule Tag T) where
  input_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).inputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      sorry
  output_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).outputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  inputs_present := by sorry
  outputs_present := by sorry

instance {Tag T} : MatchInterface  (lhs_intModule Tag T) (lhsModule Tag T) where
  input_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).inputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      sorry
  output_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).outputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  inputs_present := by sorry
  outputs_present := by sorry

#reduce rhsNames
#reduce rhsModuleType

#reduce lhsNames
#reduce lhsModuleType

#reduce lhs_intNames
#reduce lhs_intModuleType


def φ {Tag T} (state_rhs : rhsModuleType Tag T) (state_lhs : lhs_intModuleType Tag T) : Prop :=
  let ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩ := state_rhs
  let ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ := state_lhs
  x_muxT.map Prod.snd ++ x_join1_r = List.map Prod.fst (List.filter (fun x => x.2 == true) y_join_r) ++ y_muxT ∧
  x_muxF.map Prod.snd ++ x_join2_r = List.map Prod.fst (List.filter (fun x => x.2 == false) y_join_r) ++ y_muxF ∧
  x_muxC = List.map Prod.snd y_join_r ++ y_muxC ∧
  x_muxT.map Prod.fst ++ x_join1_l ++ x_fork  = y_join_l ∧
  x_muxF.map Prod.fst ++ x_join2_l ++ x_fork   = y_join_l ∧
  (y_muxC.head? = some true → y_muxT = []) ∧
  (y_muxC.head? = some false → y_muxF = [])

def φ' {Tag T} (state_rhs : rhsModuleType Tag T) (state_lhs : lhs_intModuleType Tag T) : Prop :=
  let ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩ := state_rhs
  let ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ := state_lhs
  x_join1_r ++ x_muxT.map Prod.snd  = y_muxT ++ List.filterMap (fun x => some x.1) y_join_r ∧
  x_join1_r ++ x_muxF.map Prod.snd  = y_muxF ++ List.filterMap (fun x => some x.1) y_join_r ∧
  x_muxC = y_muxC


theorem add_element {α} (l l' l'' : List α) : l ++ l' = l ++ l'' -> l' = l'' := by
  intro h
  revert h
  induction l
  . simp
  . rename_i a tail h1
    simp


theorem lhs_internal_correctness {Tag T}:
  ∀ (x : rhsModuleType Tag T) (y : lhsModuleType Tag T), φ' x y -> ∃ y',
    existSR [fun st st' =>  ∃ a b a_1 a_2 b_1 output,
              ((b_1 ++ [false] = st.2.2.2 ∧ a_1 = st.2.1 ∧ a_2 ++ [output] = st.2.2.1 ∨
              b_1 ++ [true] = st.2.2.2 ∧ a_1 ++ [output] = st.2.1 ∧ a_2 = st.2.2.1) ∧
              st.1 = (a, b)) ∧
              (st'.1.2 = output :: b ∧ st'.1.1 = a) ∧ (a_1, a_2, b_1) = st'.2] y y'
    ∧ φ x y' := by
    intro x ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ φ
    induction y_muxC using List.concat_induction generalizing y_join_r y_muxT y_muxF y_join_l x with
    | empty => sorry
    | step a b h =>
      cases a
      . cases (reverse_cases y_muxF)
        . subst_vars
          constructor; constructor
          . constructor
          . rcases φ with ⟨ φ₁, φ₂ ⟩
            simp at φ₂
            rcases φ₂ with ⟨ _, _, _, _ ⟩
            simp at φ₁
            constructor
            . simp; subst_vars; assumption
            . and_intros <;> subst_vars <;> simp <;> try assumption
              . rename_i hr
                cases x
                simp at hr
                simp; assumption
        . rename_i H; rcases H with ⟨ y_maxF, output, H ⟩
          subst_vars
          have φ' := φ
          rcases φ with ⟨ φ₁, φ₂ ⟩
          simp at φ₂
          rcases φ₂ with ⟨ _, _, _, _ ⟩
          simp at φ₁
          --specialize h x y_join_l y_join_r y_muxT y_muxF
          simp[*]
          subst_vars
          rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
          dsimp at *
          have : DataflowRewriter.MuxTaggedRewrite.φ' (x_fork, (x_muxT, x_muxF, b), (x_join1_l, x_join1_r), x_join2_l, x_join2_r) ((x_fork ++ (x_join1_l ++ List.map Prod.fst x_muxT), output :: y_join_r), y_muxT, y_maxF, b) := by

            constructor; and_intros
            skip; simp simp_all
          specialize h _ _ _ _ _ this
          rcases h with ⟨ yl, h ⟩
          apply Exists.intro ((_, _), (_, (_, _))); constructor
          . apply existSR.step _ ((_, _), (_, (_, _))) _;
            . constructor
            . constructor; constructor;constructor;
              constructor; exists b, output
              simp; and_intros
              rfl; rfl; rfl; rfl; rfl; rfl; rfl; rfl; rfl
            . apply h.left









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

set_option maxHeartbeats 0


theorem φ_indistinguishable {Tag T} :
  ∀ x y, φ x y → Module.indistinguishable (rhsModule Tag T) (lhs_intModule Tag T) x y := by
  unfold φ; intro ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩ ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ H
  dsimp at *
  constructor <;> intro ident new_i v Hcontains Hsem
  . have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      --rcases y_join with ⟨y_join_l, y_join_r⟩
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      --rcases y_join with ⟨y_join_l, y_join_r⟩
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
  · have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
    fin_cases Hkeys
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases H with ⟨ H₁, H₂, H₃, H₄, H₅, H₆, H₇ ⟩
      rcases v with ⟨ vt, vv ⟩
      rcases Hsem with ⟨ ⟨ ⟨hsemll₁, hsemll₂, hsemll₃⟩ | ⟨hsemll₁, hsemll₂, hsemll₃⟩, ⟨⟨hsemlrll, hsemlrlr⟩, ⟨hsemlrrl, hsemlrrr⟩⟩ ⟩, hsemr ⟩
      <;> subst_vars
      . rcases y_join_r with _ | ⟨y_joint_r_h, y_join_r_t⟩
        . dsimp at *; subst_vars; simp at H₇
        · rcases y_joint_r_h with ⟨y_joint_r_h_val, y_joint_r_h_bool⟩; dsimp at *; subst_vars
          simp at H₁ H₅
          symm at H₂
          symm at H₁
          have H₂' := H₂
          have H₁' := H₁

          simp at hsemll₁; rcases hsemll₁; subst_vars
          simp at H₂; cases H₂; subst_vars
        --   rw [List.map_eq_cons] at H₂
        --   rcases H₂ with ⟨el, restlist, filterlist, Hvv, H⟩
        --   rcases el with ⟨elvv, elbb⟩
        --   dsimp at *
        --   subst elvv
        --   rw [List.filter_eq_cons ] at filterlist
        --   rcases filterlist with ⟨el', restlist', filterlist', elIn1, elIn2, Hfinal⟩
        --   dsimp at *
        --   have : elbb = false := by simp_all only [beq_true, List.filter_append, List.map_append, List.append_assoc, Option.some.injEq,
        --                 Bool.false_eq_true, false_implies, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, Prod.forall,
        --                 Bool.forall_bool, imp_false, implies_true, and_true]
        -- subst elbb


          apply Exists.intro ((_, _), (_, (_, _)))
          rw [sigma_rw_simp]; dsimp
          refine ⟨⟨?_, ?_⟩, rfl⟩
          · rw [← H₅]
            have : ∀ a, List.map Prod.fst ((a, vv) :: x_new_muxF) ++ x_new_join2_l ++ x_new_fork  = a :: List.map Prod.fst (x_new_muxF) ++ x_new_join2_l ++ x_new_fork  := by simp
            rw [this]; rfl
          · left
            --simp[*] at *

            rfl
            unfold List.filter at H₂
            have H  : List.filterMap (fun x => if x.2 = false then some x else none) y_join_r ++ List.filterMap (fun x => if x.2 = true then some x else none) y_join_r = y_join_r := by unfold List.filterMap; simp
            unfold List.filterMap at H₂
            simp at H₂
            have : x_new_join2_r ++ List.map Prod.snd (x_new_muxF ++ [(vt, vv)]) = x_new_join2_r ++ List.map Prod.snd (x_new_muxF) ++ [vv] := by simp
            rw [this]
      . simp at H₆; subst_vars
        apply Exists.intro ((_, _), (_, (_, _)))
        rw [sigma_rw_simp]; dsimp
        refine ⟨⟨?_, ?_⟩, rfl⟩
        · rfl
        · right
          induction y_join_r
          . simp[*] at *
          rw[List.map_append]
          have : ∀ a, x_new_join1_r ++ (List.map Prod.snd x_new_muxT ++ a) = x_new_join1_r ++ (List.map Prod.snd x_new_muxT) ++ a := by simp
          rw [this]; rfl

theorem correct_threeway_merge'' {Tag T: Type _} [DecidableEq T]:
  rhsModule Tag T ⊑_{φ} lhsModule Tag T := by
  intro x y HPerm
  constructor
  . intro ident new_i v Hcontains Hsem
    rcases HPerm with ⟨ h₁, h₂, h₃, h₄, h₅, h₆, h₇ ⟩
    have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      .  (repeat constructor) <;> rfl
      . constructor; constructor
        . constructor
        . simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
          rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
          simp at Hsem₂
          rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
          constructor
          . simp
            subst_vars
            simp at *; assumption
          . and_intros <;> (try subst_vars) <;> (try simp[*]) <;> (try assumption)
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      . (repeat constructor) <;> rfl
      . apply lhs_internal_correctness
        simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
        rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
        simp at Hsem₂
        rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        simp at Hsem₁
        rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        constructor <;> subst_vars <;> simp[*]
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      . (repeat constructor) <;> rfl
      . apply lhs_internal_correctness
        simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
        rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
        simp at Hsem₂
        rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        simp at Hsem₁
        rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        constructor <;> subst_vars <;> simp[*]
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      . (repeat constructor) <;> rfl
      . apply lhs_internal_correctness
        simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
        rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
        simp at Hsem₂
        rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        simp at Hsem₁
        rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        constructor <;> subst_vars <;> simp[*]



end DataflowRewriter.MuxTaggedRewrite
