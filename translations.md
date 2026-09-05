# Translating to other languages

Verbose Lean currently has a French version and an English version. 
It is hopefully easy (but a bit tedious) to add more languages in separate libraries
(I do not wish to maintain versions in languages I don’t understand so I would
not merge pull requests proposing this).

You only need to copy the content of the `English` folder from this repository
and replace the English words.
In case of doubt about what needs to be done, you can look at differences
between the French and English folders.

In order to show the kind of work that is involved, here are some examples.
The easiest parts are functions like:
```lean
def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} has shape “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} starts with “{headDescr}”"


implement_endpoint (lang := en) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $nameS:ident such that ($ineqIdent : $ineqS) and ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]
```
whose French version is
```lean
def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} est de la forme « {headDescr} »"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} commence par « {headDescr} »"

implement_endpoint (lang := fr) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) et ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

```
Sometimes the surrounding Lean code looks a bit more intimidating, but the same
principle applies: look for English words that seem to be user-facing, and
compare with the French version to make sure. 
For instance, in the English version of a file we see:
```lean
declare_syntax_cat maybeApplied
syntax term : maybeApplied
syntax term "applied to " term : maybeApplied
syntax term "applied to " term " using " term : maybeApplied
syntax term "applied to " term " using that " term : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM (TSyntax `term)
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term applied to $x:term) => `($e $x)
| `(maybeApplied| $e:term applied to $x:term using $y) => `($e $x $y)
| `(maybeApplied| $e:term applied to $x:term using that $y) => 
    `($e $x (strongAssumption% $y))
| _ => pure default 

elab "We" " conclude by " e:maybeApplied : tactic => do
  concludeTac (← maybeAppliedToTerm e)
```
and the corresponding French code is:
```lean
declare_syntax_cat maybeAppliedFR
syntax term : maybeAppliedFR
syntax term "appliqué à " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant que " term : maybeAppliedFR

def maybeAppliedFRToTerm : TSyntax `maybeAppliedFR → MetaM Term
| `(maybeAppliedFR| $e:term) => pure e
| `(maybeAppliedFR| $e:term appliqué à $x:term) => `($e $x)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant $y) => `($e $x $y)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant que $y) => 
    `($e $x (strongAssumption% $y))
| _ => pure default 

elab "On" " conclut par " e:maybeAppliedFR : tactic => do
  concludeTac (← maybeAppliedFRToTerm e)
```
A note about names: the reason why the syntax category name
`maybeApplied` is translated although it is not user facing is that it is more
convenient as a library developer to be able to import both languages at the
same time. 
If you create your own translation this is less crucial. But I still recommend
doing this because you never know whether you’ll want to create a multilingual
document some day.

## A note on non-Latin scripts (this fork's Russian port)

This fork adds an unofficial Russian translation (`Verbose/Russian`, not
merged upstream, see the top of this file). Getting Cyrillic keywords to
parse at all took a bit of extra work worth documenting here for whoever
next tries a non-Latin script (Greek, Han, Arabic, Hebrew, Georgian, …).

Lean's tokenizer only accepts a curated whitelist of "letter-like" Unicode
ranges for bare identifiers and keyword atoms (`Lean.isLetterLike` in
`Init/Meta/Defs.lean`): it covers Greek, Coptic, math letter-like symbols and
accented/extended Latin, but not Cyrillic (`'П'.isAlpha` is `false`). This
alone would already block a straightforward translation into Russian, but the
actual failure mode we hit is narrower and easy to miss: a Cyrillic keyword
declared with `syntax "…" : term` or `: command` parses and works
immediately, while the exact same string declared with `syntax "…" : tactic`
(or `macro "…" : tactic => …`) silently fails to register its token — every
use then errors with `expected token`, even though the declaration itself
compiles without complaint. `term` and `command` are unaffected; the bug is
specific to the `tactic` category.

The workaround lives in `Verbose/Russian/TokenSupport.lean`: it defines a
`declare_ru_tokens` command that explicitly inserts each keyword into Lean's
token table with `Lean.Parser.addToken` (the same primitive `syntax`/
`notation` use internally), and every Russian tactic file calls it for its
own keywords before declaring them. One more wrinkle: a *multi-word* literal
such as `"Докажем по индукции, что "` is not one atom — Lean's `syntax`
sugar splits it on whitespace into separate sequential atoms ("Докажем",
"по", "индукции,", "что", each keeping any punctuation glued to it with no
preceding space) — so each resulting *word* needs registering individually,
not the combined phrase.

None of this is needed for keywords living in a custom `declare_syntax_cat`
category (as opposed to the built-in `tactic` category) — those register
fine for any script, which is why e.g. the "such that"/"applied to"-style
categories in `Verbose/Russian/Common.lean` need no such workaround.
