import Verbose.Tactics.Statements

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

-- Widget/Help have not been ported yet (see Verbose/Russian/TokenSupport.lean and the
-- project plan): rather than depending on Verbose.Russian.Widget, always fall back to
-- `without_suggestions`, exactly what Verbose/Tactics/Statements.lean does itself when
-- `config.useSuggestionWidget` is false. Once Widget is ported, replace this with a real
-- `with_suggestions%$tkp $prf` implementation, as English/French do.
implement_endpoint (lang := ru) mkWidgetProof (prf : TSyntax ``tacticSeq) (tkp : Syntax) : CoreM (TSyntax `tactic) :=
  Lean.TSyntax.mkInfoCanonical <$> `(tactic| without_suggestions%$tkp $prf)

implement_endpoint (lang := ru) victoryMessage : CoreM String := return "Победа 🎉"
implement_endpoint (lang := ru) noVictoryMessage : CoreM String := return "Упражнение не завершено."

-- Without a fuller import chain pulling in a "setLang ru" (which English/French get for
-- free by importing their Widget module), this file's own exported configuration would
-- otherwise default back to "en" — see Verbose/Russian/ExampleLib.lean and the project plan.
setLang ru

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
