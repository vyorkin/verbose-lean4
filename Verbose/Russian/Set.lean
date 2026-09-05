import Verbose.Tactics.Set
import Verbose.Russian.Common
import Verbose.Russian.TokenSupport

declare_ru_tokens "Положим"

elab "Положим " n:maybeTypedIdent " := " val:term : tactic => do
  let (n, ty) := match n with
  | `(maybeTypedIdent| $N:ident) => (N, none)
  | `(maybeTypedIdent|($N : $TY)) => (N, some TY)
  | _ => (default, none)
  setTac n ty val


setLang ru

example (a b : ℕ) : ℕ := by
  Положим n := max a b
  success_if_fail_with_msg "Имя n уже используется"
    Положим n := 1
  exact n

example (a b : ℕ) : ℕ := by
  Положим (n : ℕ) := max a b
  exact n

example : ℤ := by
  Положим (n : ℤ) := max 0 1
  exact n
