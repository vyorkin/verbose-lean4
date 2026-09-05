import Verbose.Tactics.Statements
import Verbose.Russian.Widget

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := ru) mkWidgetProof (prf : TSyntax ``tacticSeq) (tkp : Syntax) : CoreM (TSyntax `tactic) :=
  -- the token itself should have the info of `Доказательство:` so that incrementality is not
  -- disabled but the overall syntax node should have the full ref (the proof block) as
  -- canonical info so that the widget is shown on the entire block
  Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions%$tkp $prf)

implement_endpoint (lang := ru) victoryMessage : CoreM String := return "Победа 🎉"
implement_endpoint (lang := ru) noVictoryMessage : CoreM String := return "Упражнение не завершено."

/- **TODO**  Allow omitting Дано or Предположения. -/

syntax ("Упражнение"<|>"Пример") str
    "Дано:" bracketedBinder*
    "Предположения:" bracketedBinder*
    "Заключение:" term
    "Доказательство:" (tacticSeq)? "ЧТД" : command

@[incremental]
elab_rules : command
| `(command|Упражнение $_str
    Дано: $objs:bracketedBinder*
    Предположения: $hyps:bracketedBinder*
    Заключение: $concl:term
    Доказательство:%$tkp $(prf?)? ЧТД%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Пример $_str
    Дано: $objs:bracketedBinder*
    Предположения: $hyps:bracketedBinder*
    Заключение: $concl:term
    Доказательство:%$tkp $(prf?)? ЧТД%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

syntax ("Упражнение-лемма"<|>"Лемма") ident str
    "Дано:" bracketedBinder*
    "Предположения:" bracketedBinder*
    "Заключение:" term
    "Доказательство:" (tacticSeq)? "ЧТД" : command

@[incremental]
elab_rules : command
| `(command|Упражнение-лемма $name $_str
    Дано: $objs:bracketedBinder*
    Предположения: $hyps:bracketedBinder*
    Заключение: $concl:term
    Доказательство:%$tkp $(prf?)? ЧТД%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Лемма $name $_str
    Дано: $objs:bracketedBinder*
    Предположения: $hyps:bracketedBinder*
    Заключение: $concl:term
    Доказательство:%$tkp $(prf?)? ЧТД%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
