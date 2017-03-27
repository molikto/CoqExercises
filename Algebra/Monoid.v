Require Import Coq.Lists.List.

Class Monoid (A: Set) := {
  unit: A;
  comp: A -> A -> A;
  left_unity: forall x: A, comp unit x = x;
  right_unity: forall x: A, comp x unit = x;
  associtivity: forall x y z: A, comp (comp x y) z = comp x (comp y z) 
}.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x.
symmetry. trivial.
Qed.

Instance list_monoid `(A: Set) : Monoid (list A) := {
  unit := nil;
  comp := fun a b => app a b;
  left_unity := fun a => app_nil_l a;
  right_unity := fun a => app_nil_r a;
  associtivity := fun a b c => inverse (app_assoc a b c)
}.

Fixpoint comp_l {A: Set} { m: Monoid A} (l: list A): A := match l with 
  | nil => unit
  | a :: b => comp a (comp_l b)
end.

Theorem comp_l_associtivity {A: Set} {m: Monoid A} (a b: list A) : 
comp_l (app a b) = comp (comp_l a) (comp_l b).
intros. induction a. simpl. rewrite left_unity. trivial. simpl. rewrite IHa. rewrite associtivity.
trivial. Qed.