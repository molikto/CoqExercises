Require Export Induction.


Definition mynil := @nil nat.

Check @nil.

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Definition list123 := [1; 2; 3].

Fixpoint repeat {X : Type} (n: X) (cont: nat) : list X :=
  match cont with
  | O => nil
  | S prev => cons n (repeat n prev)
  end.
  
Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app: forall X: Type, forall l: list X,  [] ++ l = l.
Proof. reflexivity. Qed.

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
  | nil => cons v (@nil X)
  | cons h t => cons h (snoc t v)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => @nil X
  | cons h t => snoc (rev t) h
  end.

Theorem rev_snoc: forall X: Type, forall v: X, forall s: list X, rev (snoc s v) = v :: (rev s).
Proof. intros X. intros v. induction s as [| n h]. reflexivity. simpl. rewrite IHh. simpl. reflexivity. Qed.

Theorem rev_involutive: forall X: Type, forall l: list X, rev (rev l) = l.
Proof. intros X. induction l as [| h n]. reflexivity. simpl. rewrite rev_snoc. rewrite IHn. reflexivity. Qed.

Theorem snoc_with_append: forall X : Type, forall l1 l2: list X, forall v: X, snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof. intros X. induction l1 as [|k j]. simpl. reflexivity. simpl. intros l2 v. rewrite IHj. reflexivity. Qed.


Fixpoint filter {X: Type} (test: X -> bool) (l: list X): (list X) :=
  match l with
  | [] => []
  | h :: t => if (test h) then h :: (filter test t)
       else filter test t
  end.


Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X := ((filter test l), (filter (fun x => negb (test x)) l)).
                     
                  

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.


Definition one : nat := 
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** [two] should apply [f] twice to its argument: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.
  
Definition succ (n : nat) : nat :=
  fun (X: Type) (f: X -> X) (x : X) => f (n X f x).


Definition three : nat := succ two.

Definition plus (n m : nat) : nat :=
 fun (X: Type) (f: X -> X) (x: X) => 
  (n X f (m X f x)).
  
Definition mult (n m : nat) : nat := 
  fun (X: Type) (f: X -> X) (x: X) =>
  (m X (fun (x: X) => (n X f x)) x).
  
Example mult_1 : mult one one = one.
Proof. unfold mult. unfold one. unfold plus. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.


Definition exp (n m : nat) : nat :=
  fun (X: Type) (f: X -> X) (x: X) =>
    let T := (X -> X) -> X -> X
     in
      let mult2 := (fun (a: T) (b: T) => (fun (f: X -> X) (x: X) => (a (fun (x: X) => (b f x)) x)))
        in ((m T (fun (a: T) => (mult2 a (n X))) (one X)) f x).
  
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.


