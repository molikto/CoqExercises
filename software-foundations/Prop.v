Require Export Logic.



Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).
  
Fixpoint double (n: nat) := match n with
  | O => O
  | S k => S (S (double k))
  end.


Theorem double_even : forall n,
  ev (double n).
Proof. induction n. simpl. constructor. simpl. constructor. trivial. Qed.

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


Theorem three_is_beautiful: beautiful 3.
Proof.
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).

   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof. intros. simpl. replace(n + (n + 0)) with (n + n). apply b_sum with (m:=n) (n:=n). trivial. trivial. auto. Qed.

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof. induction m. simpl. intros. constructor. simpl. intros. set H. apply IHm in b. constructor. trivial. trivial. Qed. 

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).


Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof. intros. destruct n. apply g_plus5 in H. apply g_plus5 in H. apply g_plus3 in H. simpl in H. simpl. trivial. apply g_plus5 in H. apply g_plus5 in H. apply g_plus3 in H. simpl in H. simpl. trivial. Qed.
  


Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
       apply b_0.
       apply b_sum. apply b_3.
       apply IHgorgeous.
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof. intros. induction H. simpl. trivial. apply g_plus3 in IHgorgeous. simpl. simpl in IHgorgeous. trivial. apply g_plus5 in IHgorgeous. simpl. simpl in IHgorgeous. trivial. Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof. intros. induction H. constructor. constructor. constructor. apply g_plus5. constructor. apply gorgeous_sum. trivial. trivial. Qed.



Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. intros. induction H; induction H0. simpl. constructor. simpl. constructor. trivial. replace ((S (S n)) + 0) with (S (S n)). replace (n + 0) with n in IHev. constructor. trivial. auto. auto. replace (S (S n) + S (S n0)) with (S (S (n + (S (S n0))))). constructor. trivial. auto. Qed. 

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  destruct E as [| n' E'].
  simpl. apply ev_0. 
  simpl. apply E'.  Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  inversion E'.
  trivial.
  Qed.

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3. Qed.


Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof. intros. induction H0. simpl in H. trivial. inversion H. apply IHev in H2. trivial. Qed. 



Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc".  simpl.  apply ev_SS. apply IHev_list.
Qed.


Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
  Case "ev_0". intros l H. destruct l.
    SCase "[]". apply el_nil. 
    SCase "x::l". inversion H.
  Case "ev_SS". intros l H2. destruct l. 
    SCase "[]". inversion H2. destruct l.
    SCase "[x]". inversion H2.
    SCase "x :: x0 :: l". apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.


Inductive pal {X: Type}: list X -> Prop :=
  | empty: pal []
  | single: forall a: X, pal [a]
  | other: forall l: list X, forall p: pal l, forall val: X, pal ([val] ++ l ++ [val]).
  
Require Import Coq.Lists.List.


Goal forall X: Type, forall l: list X, pal (l ++ rev l).
Proof. intros. induction l. simpl. constructor. replace ((a :: l) ++ rev (a :: l)) with ([a] ++ (l ++ rev l) ++ [a]). constructor. trivial. simpl. assert (forall l: list X, forall a, (snoc (l) a = l ++ [a])). induction l0. reflexivity. simpl. intros a1. rewrite IHl0. reflexivity. assert ((l ++ rev l) ++ [a] = l ++ rev l ++ [a]). set (app_assoc l (rev l) [a]). symmetry. trivial. rewrite H0. reflexivity. Qed.


Goal forall t l, pal l -> @rev t l = l.
Proof. intros. induction H. trivial. trivial. simpl. rewrite rev_unit. rewrite IHpal. reflexivity. Qed.

Fixpoint last {X: Type}  (h: X) (t: list X) :=
  match t with
  | [] => h
  | a :: b => last a b
  end.

Fixpoint front {X: Type} (h: X) (t: list X) :=
  match t with 
  | [] => []
  | a:: b => h :: (front a b)
  end.
  

Definition shift: forall (X: Type) (a: X) (b: list X), exists (c: list X) (d: X), a :: b = snoc c d. intros. destruct b. exists []. exists a. trivial. exists (front a (x :: b)). exists (last a (x :: b)). generalize dependent a. generalize dependent x. induction b. trivial. simpl. intros. set (IHb a x). assert (snoc (front x (a :: b)) (last x (a :: b)) = x :: (snoc (front a b) (last a b))). simpl. trivial. rewrite H in e. rewrite e. trivial. Qed.

Theorem snoc_app: forall (X: Type) (f: list X) (a: X), snoc f a = f ++ [a].
Proof. intros. induction f. trivial. simpl. rewrite IHf. trivial. Qed.

Theorem list_triple_rec {X: Type} (p: list X -> Prop) (p0: (p nil)) (p1: forall a: X, (p [a])) (pn: forall a b: X, forall k: list X, (p k) -> (p (a :: (k ++ [b])))): (forall l: list X, (p l)).
Proof. destruct l. trivial. destruct l. trivial. set (shift X x0 l). inversion e. inversion H. rewrite H0. clear H0. clear H. clear e. clear l. clear x0. induction x1. simpl. apply (pn x x2 []). trivial. set (shift X a x1). inversion e. inversion H. rewrite H0. clear H0. clear H. clear e. 
admit. Qed.


Goal forall t l, @rev t l = l -> pal l.
Proof. intros t. refine (list_triple_rec (fun (l: list t) => rev l = l -> pal l) _ _ _). intros. constructor. intros. constructor. intros. simpl in H0. rewrite rev_unit in H0. inversion H0. subst. inversion H0. Abort.


Module LeModule.  



Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive total_relation: nat -> nat -> Prop := | tttt : forall n m: nat, total_relation n m.

Inductive empty_relation: nat -> nat -> Prop := .


Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof. intros. induction H0. trivial. apply IHle in H. constructor. trivial. Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof. induction n. constructor. constructor. trivial. Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. intros. induction H. constructor. constructor. trivial. Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. intros. inversion H. subst. constructor. subst. assert (n <= S n). constructor. constructor. apply (le_trans n (S n) m H0 H2). Qed. 


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.  induction b. rewrite plus_n_O. constructor. rewrite <- plus_n_Sm. constructor. trivial. Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.   

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, optional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 3 stars (R_provability2)  *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)  
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function. 
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

(* FILL IN HERE *)
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is, 
      any list is a subsequence of itself.  

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3], 
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is 
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2] 
      is a subsequence of [l3], then [l1] is a subsequence of [l3].  
      Hint: choose your induction carefully!
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability)  *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(** [] *)


(* ##################################################### *)
(** * Programming with Propositions *)

(** As we have seen, a _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop]. . *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** *** *)
(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere)  *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

(* 
Fixpoint true_upto_n__true_everywhere
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

