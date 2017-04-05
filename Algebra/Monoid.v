Require Import Coq.Lists.List.

Class Monoid `(A: Set) := {
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
Proof. intros. induction a. simpl. rewrite left_unity. trivial. simpl. rewrite IHa. rewrite associtivity.
trivial. Qed.

Class AbelianMonoid  `(A: Set) := {
  AbelianMonoid_Monoid :> Monoid A;
  commutative: forall a b: A, comp a b = comp b a
}.

Require Import Coq.Sorting.Permutation.


Theorem abelian_comp {A: Set} { m: AbelianMonoid A} (l l': list A)
(perm: Permutation l l'): comp_l l = comp_l l'.
Proof. induction perm. trivial. simpl. rewrite IHperm.
trivial. simpl. rewrite <- associtivity. rewrite <- associtivity.
assert ((comp y x) = (comp x y)). rewrite commutative. trivial.
rewrite H. trivial. rewrite IHperm1. rewrite IHperm2. trivial. Qed.

Fixpoint monoid_pow {A: Set} { m: Monoid A} (x: A) (n: nat) := match n with
  | 0 => unit
  | S m => comp x (monoid_pow x m)
end.

Theorem monoid_pow_associtivity  {A: Set} {m: Monoid A} (a b: nat) (x: A) :
monoid_pow x (a + b) = comp (monoid_pow x a) (monoid_pow x b).
Proof. induction a. simpl. rewrite left_unity. trivial. simpl. rewrite IHa.
rewrite associtivity. trivial. Qed.


Theorem monoid_pow_commutative  {A: Set} {m: AbelianMonoid A} (a: nat) (x y: A) :
monoid_pow (comp x y) a = comp (monoid_pow x a) (monoid_pow y a).
Proof. induction a. simpl. rewrite left_unity. trivial. simpl. rewrite IHa.
rewrite associtivity. rewrite associtivity. 
assert (comp y (comp (monoid_pow x a) (monoid_pow y a)) = comp (monoid_pow x a) (comp y (monoid_pow y a))).
rewrite commutative. rewrite associtivity. replace (comp (monoid_pow y a) y) with (comp y (monoid_pow y a)).
trivial. rewrite commutative. trivial. rewrite H. trivial. Qed.

Class Group `(A: Set) := {
 Group_Monoid :> Monoid A;
 has_inverse: forall x: A, exists y: A, comp x y = unit
}.


