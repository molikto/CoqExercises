Inductive Unit := unit.

Inductive Bottom := .

Class Poset (S: Set) := {
  lt: forall a b: S, Type;
  lt_nonReflective: forall p: S, p = p -> (lt p p) -> Bottom;
  lt_transitive: forall a b c: S, (lt a b) -> (lt b c) -> (lt a c)
}.

Instance nat_poset : Poset net :=
{
  lt: (a b: nat) => Type := 
}