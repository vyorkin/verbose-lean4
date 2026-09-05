import Verbose.Tactics.Widget
import Verbose.Russian.Help

namespace Verbose.Russian
open Lean Meta Server

open ProofWidgets

implement_endpoint (lang := ru) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Переформулируем $hyp как $new)

implement_endpoint (lang := ru) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Докажем, что $new)

implement_endpoint (lang := ru) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeApplied args
`(tactic|Заключаем по $concl)

implement_endpoint (lang := ru) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeApplied args
let newStuff ← listMaybeTypedIdentToNewStuffSuchThatRU news
`(tactic|По $maybeApp получаем $newStuff)

implement_endpoint (lang := ru) mkSinceConcludeTacStx (args : List Term) (goalS : Term) : MetaM (TSyntax `tactic) := do
let concl ← arrayToFactsRU args.toArray
`(tactic|Поскольку $concl заключаем, что $goalS)

-- FIXME: the code below is probably too specific. Need something more principled
implement_endpoint (lang := ru) mkSinceObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
    MetaM (TSyntax `tactic) := do
  let facts ← arrayToFactsRU args.toArray
  match news with
  | [(_, some stmt)] =>
      `(tactic|Поскольку $facts получаем, что $stmt:term)
  | _ =>
      let newStuff ← listMaybeTypedIdentToNewObjectNameLessRU news
      `(tactic|Поскольку $facts получаем $newStuff:newObjectNameLessRU)

implement_endpoint (lang := ru) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Докажем, что $wit подходит: $goal)
| none => `(tactic|Докажем, что $wit подходит)

implement_endpoint (lang := ru) mkSinceTacStx (facts : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsS ← arrayToFactsRU facts
  `(tactic|Поскольку $factsS заключаем, что $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Используйте shift-клик, чтобы выделить подвыражения."
  "Предложения"
  "suggestions"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions, incremental]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx => do
    Elab.Term.withNarrowedArgTacticReuse 1 Lean.Elab.Tactic.evalTacticSeq stx
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx

end Verbose.Russian
