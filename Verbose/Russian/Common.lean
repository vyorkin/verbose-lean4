import Verbose.Tactics.Common
import Verbose.Russian.TokenSupport

open Lean

namespace Verbose.Russian

declare_ru_tokens "рефл"

/-- Russian spelling of the `rfl` tactic, short for "рефлексивность" (reflexivity),
so that a bare Latin `rfl` doesn't stand out in the middle of a Cyrillic proof. -/
macro "рефл" : tactic => `(tactic| rfl)

declare_syntax_cat appliedToRU
syntax "применённый к " sepBy(term, " и ") : appliedToRU

def appliedToRUTerm : TSyntax `appliedToRU → Array Term
| `(appliedToRU| применённый к $[$args]и*) => args
| _ => default -- This will never happen as long as nobody extends appliedToRU

declare_syntax_cat usingStuffRU
syntax " используя " sepBy(term, " и ") : usingStuffRU
syntax " используя, что " term : usingStuffRU

def usingStuffRUToTerm : TSyntax `usingStuffRU → Array Term
| `(usingStuffRU| используя $[$args]и*) => args
| `(usingStuffRU| используя, что $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends usingStuffRU

declare_syntax_cat maybeAppliedRU
syntax term (appliedToRU)? (usingStuffRU)? : maybeAppliedRU

def maybeAppliedRUToTerm : TSyntax `maybeAppliedRU → MetaM Term
| `(maybeAppliedRU| $e:term) => pure e
| `(maybeAppliedRU| $e:term $args:appliedToRU) => `($e $(appliedToRUTerm args)*)
| `(maybeAppliedRU| $e:term $args:usingStuffRU) => `($e $(usingStuffRUToTerm args)*)
| `(maybeAppliedRU| $e:term $args:appliedToRU $extras:usingStuffRU) =>
  `($e $(appliedToRUTerm args)* $(usingStuffRUToTerm extras)*)
| _ => pure default -- This will never happen as long as nobody extends maybeAppliedRU

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments. When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeApplied : List Term → MetaM (TSyntax `maybeAppliedRU)
| [x] => `(maybeAppliedRU|$x:term)
| [x, y] => `(maybeAppliedRU|$x:term применённый к $y)
| [x, y, z] => `(maybeAppliedRU|$x:term применённый к $y используя, что $z)
| x::y::l => `(maybeAppliedRU|$x:term применённый к $y:term используя [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffRU
syntax (ppSpace colGt maybeTypedIdent)* : newStuffRU
syntax maybeTypedIdent "такой, что" ppSpace colGt maybeTypedIdent : newStuffRU
syntax maybeTypedIdent "такой, что" ppSpace colGt maybeTypedIdent " и "
       ppSpace colGt maybeTypedIdent : newStuffRU

def newStuffRUToArray : TSyntax `newStuffRU → Array MaybeTypedIdent
| `(newStuffRU| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffRU| $x:maybeTypedIdent такой, что $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuffRU| $x:maybeTypedIdent такой, что $y:maybeTypedIdent и $z) =>
    Array.map toMaybeTypedIdent #[x, y, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatRU : List MaybeTypedIdent → MetaM (TSyntax `newStuffRU)
| [x] => do `(newStuffRU| $(← x.stx):maybeTypedIdent)
| [x, y] => do `(newStuffRU| $(← x.stx):maybeTypedIdent такой, что $(← y.stx'))
| [x, y, z] => do `(newStuffRU| $(← x.stx):maybeTypedIdent такой, что $(← y.stx) и $(← z.stx))
| _ => pure default

declare_syntax_cat factsRU
syntax term : factsRU
syntax term " и " term : factsRU
syntax term ", " term " и " term : factsRU
syntax term ", " term ", " term " и " term : factsRU

def factsRUToArray : TSyntax `factsRU → Array Term
| `(factsRU| $x:term) => #[x]
| `(factsRU| $x:term и $y:term) => #[x, y]
| `(factsRU| $x:term, $y:term и $z:term) => #[x, y, z]
| `(factsRU| $x:term, $y:term, $z:term и $w:term) => #[x, y, z, w]
| _ => #[]

def arrayToFactsRU : Array Term → CoreM (TSyntax `factsRU)
| #[x] => `(factsRU| $x:term)
| #[x, y] => `(factsRU| $x:term и $y:term)
| #[x, y, z] => `(factsRU| $x:term, $y:term и $z:term)
| #[x, y, z, w] => `(factsRU| $x:term, $y:term, $z:term и $w:term)
| _ => default

def factsRUToTypeTerm : TSyntax `factsRU → MetaM Term
| `(factsRU| $x:term) => `($x)
| `(factsRU| $x:term и $y) => `($x ∧ $y)
| `(factsRU| $x:term, $y:term и $z) => `($x ∧ $y ∧ $z)
| _ => throwError "Не удалось преобразовать описание новых фактов в терм."

/-- Convert an expression to a `maybeAppliedRU` syntax object, in `MetaM`. -/
def _root_.Lean.Expr.toMaybeAppliedRU (e : Expr) : MetaM (TSyntax `maybeAppliedRU) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeAppliedRU|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeAppliedRU|$fnS:term применённый к $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeAppliedRU|$fnS:term применённый к [$arr:term,*])

declare_syntax_cat newObjectNameLessRU
syntax maybeTypedIdent "такой, что " term : newObjectNameLessRU
syntax maybeTypedIdent "такой, что " term colGt " и " term : newObjectNameLessRU
syntax maybeTypedIdent "такой, что " term ", " colGt term colGt " и " term : newObjectNameLessRU

syntax telsChtoRU := "такой, что " <|> "такие, что "

syntax maybeTypedIdent " и " maybeTypedIdent telsChtoRU term : newObjectNameLessRU
syntax maybeTypedIdent " и " maybeTypedIdent telsChtoRU term colGt " и " term : newObjectNameLessRU
syntax maybeTypedIdent " и " maybeTypedIdent telsChtoRU term ", " colGt term colGt " и " term : newObjectNameLessRU

def newObjectNameLessRUToLists : TSyntax `newObjectNameLessRU → (List (TSyntax `maybeTypedIdent) × List Term)
| `(newObjectNameLessRU| $x:maybeTypedIdent такой, что $new) =>
  ([x], [new])
| `(newObjectNameLessRU| $x:maybeTypedIdent такой, что $new₁ и $new₂) =>
  ([x], [new₁, new₂])
| `(newObjectNameLessRU| $x:maybeTypedIdent такой, что $new₁, $new₂ и $new₃) =>
  ([x], [new₁, new₂, new₃])
| `(newObjectNameLessRU| $x:maybeTypedIdent и $y:maybeTypedIdent $_ $new) =>
  ([x, y], [new])
| `(newObjectNameLessRU| $x:maybeTypedIdent и $y:maybeTypedIdent $_ $new₁ и $new₂) =>
  ([x, y], [new₁, new₂])
| `(newObjectNameLessRU| $x:maybeTypedIdent и $y:maybeTypedIdent $_ $new₁, $new₂ и $new₃) =>
  ([x, y], [new₁, new₂, new₃])
| _ => default

def newObjectNameLessRUToTerm (no : TSyntax `newObjectNameLessRU) : MetaM Term :=
  let (xs, news) := newObjectNameLessRUToLists no
  newObjNlToTerm xs news

def newObjectNameLessRUToArray (no : TSyntax `newObjectNameLessRU) : Array MaybeTypedIdent :=
  let (xs, news) := newObjectNameLessRUToLists no
  newObjNlToArray xs news

open Tactic Lean.Elab.Tactic.RCases in
def newObjectNameLessRUToRCasesPatt (no : TSyntax `newObjectNameLessRU) : RCasesPatt :=
  let (xs, news) := newObjectNameLessRUToLists no
  newObjNlToRCasesPatt xs news

def listMaybeTypedIdentToNewObjectNameLessRU : List MaybeTypedIdent → MetaM (TSyntax `newObjectNameLessRU)
| [(x, some t), (_, some s)] => do `(newObjectNameLessRU| ($(mkIdent x):ident : $t) такой, что $s)
| [(x, none), (_, some s)] => do `(newObjectNameLessRU| $(mkIdent x):ident такой, что $s)
| [(x, none), (_, some s), (_, some r)] => do `(newObjectNameLessRU| $(mkIdent x):ident такой, что $s и $r)
| [(x, some t), (_, some s), (_, some r)] => do `(newObjectNameLessRU| ($(mkIdent x):ident : $t) такой, что $s и $r)
| _ => pure default

implement_endpoint (lang := ru) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"Имя {n} уже используется"

implement_endpoint (lang := ru) notDefEq (e val : MessageData) : CoreM MessageData :=
pure m!"Данный терм{e}\nне равен по определению ожидаемому{val}"

implement_endpoint (lang := ru) notAppConst : CoreM String :=
pure "Это не применение определения."

implement_endpoint (lang := ru) cannotExpand : CoreM String :=
pure "Не удалось развернуть определение головного символа."

implement_endpoint (lang := ru) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"Похоже, что {tgt} не следует непосредственно не более чем из одного локального предположения."

implement_endpoint (lang := ru) couldNotProve (goal : Format) : CoreM String :=
pure s!"Не удалось доказать:\n{goal}"

implement_endpoint (lang := ru) failedProofUsing (goal : Format) : CoreM String :=
pure s!"Не удалось доказать это, используя предоставленные факты.\n{goal}"
