/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module

namespace DataflowRewriter

@[simp]
def io (T : Type) : Module (List T) :=
  { inputs := [(0, ⟨ T, λ s t s' => s' = t :: s ⟩)].toAssocList,
    internals := [],
    outputs := [(0, ⟨ T, λ s t s' => s = s' ++ [t] ⟩)].toAssocList
  }

@[simp]
def merge_inputs {S} (mod : Module S) (in1 in2 : InternalPort Nat) : Option (Module S)  := do
  let in1_t ← mod.inputs.find? in1;
  let in2_t ← mod.inputs.find? in2;
  let rmin2 := mod.inputs.erase in2;
  some { inputs :=
         rmin2.cons in2 ⟨ in1_t.1 × in2_t.1, λ s (v1,v2) s' =>
               ∃ s_int, in1_t.2 s v1 s_int ∧
               in2_t.2 s_int v2 s'⟩,
         outputs := mod.outputs,
         internals := mod.internals }

@[simp]
def merge_outputs {S} (mod : Module S) (out1 out2 : InternalPort Nat) : Option (Module S)  := do
  let out1_t ← mod.outputs.find? out1;
  let out2_t ← mod.outputs.find? out2;
  let rmout2 := mod.outputs.erase out2;
      some { outputs :=
               rmout2.cons out2 ⟨ out1_t.1 × out2_t.1, λ s (v1,v2) s' =>
                   ∃ s_int, out1_t.2 s v1 s_int ∧
                   out2_t.2 s_int v2 s' ⟩,
             inputs := mod.inputs,
             internals := mod.internals }

@[simp]
def merge T : Module (List T) :=
      { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
                   (1, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
        outputs := [(0, ⟨ T, λ oldList oldElement newList => 
                           ∃ i, newList = oldList.remove i 
                             ∧ oldElement = oldList.get i ⟩)].toAssocList,
        internals := []
      }

@[simp]
def fork T : Module (List T) :=
      { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
        outputs := [ (0, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   , (1, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   ].toAssocList,
        internals := []
      }

end DataflowRewriter
