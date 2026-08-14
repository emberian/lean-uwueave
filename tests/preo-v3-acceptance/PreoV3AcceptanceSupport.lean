/-
# PreoV3AcceptanceSupport — test-only environment assertions

The Wave-26 acceptance suite compiles every fixture in a fresh Lean process.
These commands assert the only transactional state visible to a downstream
consumer: whether a generated declaration exists after success or failure.
This module is intentionally outside the public `Uwueave` module tree.
-/
import Lean
import Uwueave.Preo.ArtifactV3Surface

namespace PreoV3AcceptanceSupport

open Lean Elab Command

syntax "#assert_decl " ident : command
syntax "#assert_no_decl " ident : command
syntax "#assert_v3_failed_info_clean " ident " in " command : command
syntax "#assert_v3_success_info_clean " ident " in " command : command

elab_rules : command
  | `(command| #assert_decl $decl:ident) => do
      let name ← resolveGlobalConstNoOverload decl
      unless (← getEnv).contains name do
        throwErrorAt decl "expected declaration `{name}` to be present"
  | `(command| #assert_no_decl $decl:ident) => do
      let candidate := (← getCurrNamespace) ++ decl.getId
      if (← getEnv).contains candidate then
        throwErrorAt decl "expected declaration `{candidate}` to be absent"

/-- Run the registered V3 elaborator through a failing command and assert that
its transaction retains only the wrapper's single outer command tree, with no
declarations or generated/pending info state.  Its original error log is
restored before aborting for the surrounding diagnostic canary. -/
def assertV3FailedInfoClean (declPrefix : Name) (cmd : Syntax) : CommandElabM Unit := do
  let beforeInfo ← getInfoState
  unless beforeInfo.enabled && beforeInfo.assignment.isEmpty &&
      beforeInfo.lazyAssignment.isEmpty do
    throwErrorAt cmd "expected no pending information-tree assignments before V3 failure"
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  elabCommand cmd
  let localMessages := (← get).messages
  modify fun state => { state with messages := savedMessages }
  unless localMessages.hasErrors do
    throwErrorAt cmd "expected the checked V3 export to fail"
  let afterInfo ← getInfoState
  unless afterInfo.trees.size == beforeInfo.trees.size + 1 &&
      afterInfo.enabled && afterInfo.assignment.isEmpty &&
      afterInfo.lazyAssignment.isEmpty do
    throwErrorAt cmd "failed V3 export retained generated or pending information trees: \
      trees {beforeInfo.trees.size} -> {afterInfo.trees.size}, \
      enabled {beforeInfo.enabled} -> {afterInfo.enabled}, \
      assignments {beforeInfo.assignment.toList.length} -> \
        {afterInfo.assignment.toList.length}, lazy \
      {beforeInfo.lazyAssignment.toList.length} -> \
        {afterInfo.lazyAssignment.toList.length}"
  let fullPrefix := (← getCurrNamespace) ++ declPrefix
  let leaked := (← getEnv).constants.toList.any fun (name, _) =>
    fullPrefix.isPrefixOf name
  if leaked then
    throwErrorAt cmd "failed V3 export retained a generated declaration"
  modify fun state => { state with messages := savedMessages ++ localMessages }
  throwAbortCommand

/-- A successful registered export likewise retains exactly one outer command
tree, restores information recording, and publishes exactly the 37 declared
environment names pinned by the Wave-27 golden. -/
def assertV3SuccessInfoClean (declPrefix : Name) (cmd : Syntax) : CommandElabM Unit := do
  let beforeInfo ← getInfoState
  unless beforeInfo.enabled && beforeInfo.assignment.isEmpty &&
      beforeInfo.lazyAssignment.isEmpty do
    throwErrorAt cmd "expected no pending information-tree assignments before V3 success"
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  elabCommand cmd
  let localMessages := (← get).messages
  modify fun state => { state with messages := savedMessages ++ localMessages }
  if localMessages.hasErrors then
    throwAbortCommand
  let afterInfo ← getInfoState
  unless afterInfo.trees.size == beforeInfo.trees.size + 1 &&
      afterInfo.enabled && afterInfo.assignment.isEmpty &&
      afterInfo.lazyAssignment.isEmpty do
    throwErrorAt cmd "successful V3 export retained generated or pending information trees: \
      trees {beforeInfo.trees.size} -> {afterInfo.trees.size}, \
      enabled {beforeInfo.enabled} -> {afterInfo.enabled}, \
      assignments {beforeInfo.assignment.toList.length} -> \
        {afterInfo.assignment.toList.length}, lazy \
      {beforeInfo.lazyAssignment.toList.length} -> \
        {afterInfo.lazyAssignment.toList.length}"
  let fullPrefix := (← getCurrNamespace) ++ declPrefix
  let published := (← getEnv).constants.toList.countP fun (name, _) =>
    fullPrefix.isPrefixOf name
  unless published == 37 do
    throwErrorAt cmd "successful V3 export published {published} prefix declarations; expected 37"

elab_rules : command
  | `(#assert_v3_failed_info_clean $declPrefix:ident in $cmd:command) =>
      assertV3FailedInfoClean declPrefix.getId cmd
  | `(#assert_v3_success_info_clean $declPrefix:ident in $cmd:command) =>
      assertV3SuccessInfoClean declPrefix.getId cmd

end PreoV3AcceptanceSupport
