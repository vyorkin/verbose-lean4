import Lean

/-!
Lean's `tactic` syntax category currently fails to register keyword atoms whose first
character is outside `Lean.isLetterLike` (Cyrillic is not covered, unlike Greek letters
or accented Latin — see https://github.com/leanprover/lean4/issues/700 for background on
why the set of "letter-like" characters is a curated whitelist rather than full Unicode).
Concretely: `syntax "Пусть " ... : tactic` and `macro "Пусть " ... : tactic => ...` both
elaborate without error, but the literal token "Пусть" never lands in the environment's
token table (`Lean.Parser.getTokenTable`), so the tactic parser reports `expected token`
at every use site. The exact same string works fine as a `term` or `command` keyword, and
in any custom `declare_syntax_cat` category — this is specific to the built-in `tactic`
category.

The workaround is to explicitly insert the token with `Lean.Parser.addToken`, which is the
same primitive `syntax`/`notation` use internally. Every Russian tactic keyword (and every
literal atom that is part of a `: tactic` production) must be registered here before use.

Important: a multi-word string literal such as `"Докажем по индукции, что "` is NOT one
atom — Lean's `syntax`/`macro`/`elab` sugar splits it on whitespace into separate
sequential atoms ("Докажем", "по", "индукции,", "что", each keeping any punctuation
glued to it with no intervening space). Register each resulting *word* individually,
never the combined phrase — registering a combined multi-word string creates a token
that greedily shadows the correct word-by-word match anywhere else that same word
sequence appears (including in unrelated `term`/`command` syntax), breaking its parsing.
-/

open Lean Elab Command in
/-- Register one or more string literals as valid tokens for the `tactic` parser. Required
for every Cyrillic keyword atom used in a `: tactic` syntax/macro declaration in this
language pack (see the module doc above for why). -/
elab "declare_ru_tokens " tks:str+ : command => do
  for tk in tks do
    liftCoreM <| Lean.Parser.addToken tk.getString AttributeKind.global
