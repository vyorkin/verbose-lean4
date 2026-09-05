import Verbose.Russian.Common
import Verbose.Russian.Fix
import Verbose.Russian.TokenSupport

open Lean Elab Tactic

declare_ru_tokens "Предположим₁" "Предположим" "Предположим," "от" "противного"
  "противного," "что" "и"

syntax "Предположим₁ " colGt assumeDecl : tactic
elab_rules : tactic
  | `(tactic| Предположим₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Предположим₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Предположим₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Предположим₁ $decl:assumeDecl))


namespace Verbose.Named
scoped syntax "Предположим " (colGt assumeDecl)+ : tactic
scoped syntax "Предположим " "от противного " (colGt assumeDecl) : tactic

scoped macro_rules
  | `(tactic| Предположим $decl:assumeDecl) => `(tactic| Предположим₁ $decl)
  | `(tactic| Предположим $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Предположим₁ $decl; Предположим $decls:assumeDecl*)

scoped elab_rules : tactic
  | `(tactic| Предположим от противного $x:ident : $type) => forContradiction x.getId type

example (P Q : Prop) : P → Q → True := by
  Предположим hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Предположим hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Предположим hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "Здесь нет предположения для введения."
    Предположим n
  intro n
  Предположим H : n > 0
  trivial


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Предположим hP
  Предположим от противного hnQ :¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Предположим hP
  Предположим от противного hnQ : ¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q := by
  Предположим hP
  Предположим hnQ : Q
  exact h hnQ hP

example : ∀ n > 0, n = n := by
  Предположим от противного H : ∃ n > 0, n ≠ n
  tauto

private def foo_bar (P : Nat → Prop) := ∀ x, P x

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  success_if_fail_with_msg
    "Это не то, что нужно предполагать от противного, даже после внесения отрицаний."
    Предположим от противного H : ∃ x, ¬ P x
  unfold foo_bar
  Предположим от противного H : ∃ x, ¬ P x
  exact h H

configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  Предположим от противного H : ∃ x, ¬ P x
  exact h H

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "Цель уже является отрицанием, доказывать её от противного бессмысленно. Можно сразу предположить 0 = 1."
    Предположим от противного h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Предположим h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Предположим от противного h : 0 = 1
  norm_num at h

-- Check type ascriptions are not needed
example : ¬ (2 : ℝ) * -42 = 2 * 42 := by
  Предположим hyp : 2 * -42 = 2 * 42
  linarith
end Verbose.Named

namespace Verbose.NameLess
syntax "Предположим, что " (colGt term) : tactic
syntax "Предположим, что " (colGt term " и " term) : tactic
syntax "Предположим, что " (colGt term ", " term " и " term) : tactic
syntax "Предположим " "от противного, что " (colGt term) : tactic

elab_rules : tactic
  | `(tactic| Предположим, что $t) => withMainContext do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
  | `(tactic| Предположим, что $t и $s) => withMainContext do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
     let e ← elabTerm s none
     let name ← mk_hyp_name s e
     Assume1 (introduced.typed (mkNullNode #[s]) name s)
  | `(tactic| Предположим, что $t, $s и $r) => withMainContext do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
     let e ← elabTerm s none
     let name ← mk_hyp_name s e
     Assume1 (introduced.typed (mkNullNode #[s]) name s)
     let e ← elabTerm r none
     let name ← mk_hyp_name r e
     Assume1 (introduced.typed (mkNullNode #[r]) name r)


elab_rules : tactic
  | `(tactic| Предположим от противного, что $t) => withMainContext do
    let e ← elabTerm t none
    let name ← mk_hyp_name t e
    forContradiction name t


example (P : Prop) : P → True := by
  success_if_fail_with_msg "Данный терм
  True
не равен по определению ожидаемому
  P"
    Предположим, что True
  Предположим, что P
  success_if_fail_with_msg "Здесь нет предположения для введения."
    Предположим, что True
  trivial

example (P Q : Prop) : P → Q → True := by
  Предположим, что P и Q
  trivial

example (P Q R : Prop) : P → Q → R → True := by
  Предположим, что P, Q и R
  trivial

end Verbose.NameLess
