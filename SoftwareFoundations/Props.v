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

Require Import Coq.Lists.List.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof. intros. induction H0. simpl in H. trivial. inversion H. apply IHev in H2. trivial. Qed.



Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list nil
  | el_cc  : forall x y l, ev_list l -> ev_list (cons x (cons y l)).

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
     simpl. apply ev_0.
      simpl.  apply ev_SS. apply IHev_list.
Qed.


Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
   intros l H. destruct l.
     apply el_nil. 
     inversion H.
   intros l H2. destruct l. 
     inversion H2. destruct l.
     inversion H2.
     apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.


Inductive pal {X: Type}: list X -> Prop :=
  | empty: pal nil
  | single: forall a: X, pal [a]
  | other: forall l: list X, forall p: pal l, forall val: X, pal ([val] ++ l ++ [val]).
  


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


Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Theorem list_length_0: forall (T: Type) (l: list T), (length l = 0) -> l = [].
Proof. intros. destruct l. trivial. simpl in H. inversion H. Qed. 


Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive total_relation: nat -> nat -> Prop := | tttt : forall n m: nat, total_relation n m.

Inductive empty_relation: nat -> nat -> Prop := .


Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof. intros. induction H0. trivial. apply IHle in H. constructor. trivial. Qed.

Theorem le_0_n: forall (n: nat), le 0 n.
Proof. induction n. constructor. set (le_S 0 n IHn). trivial. Qed.

Theorem le_S_n: forall (m n: nat), (le (S m) n) -> (le m n).
Proof. intros. assert (le m (S m)). constructor. constructor. set (le_trans m (S m) n). apply l. trivial. trivial. Qed.

Theorem le_n_S: forall (m n: nat), (le m n) -> (le m (S n)).
Proof. intros. constructor. trivial.  Qed.

Theorem le_S_S: forall (m n: nat), (le (S m) (S n)) <-> (le m n).
Proof. split. intros. inversion H. constructor. subst. apply le_S_n in H2. trivial. intros. induction H. constructor. assert (S m <= S( S m)). constructor. constructor. set (le_trans (S n) (S m) (S (S m))). apply l. trivial. trivial. Qed.

Theorem generalized_list_induction: 
    forall 
      (T: Type)
      (p: list T -> Prop)
      (p0: p nil) 
      (pn: forall
        (n: nat),
          (forall (j: list T), (le (S (length j)) n) -> p j) ->
        (forall (l: list T), length l = n -> p l))
      , (forall (l: list T), p l).
Proof. intro. intro. intro. intro. assert (forall n: nat,
  (forall (l: list T) (nleq: le (length l) n), p l) /\
  ((forall (l: list T) (nleq: le (length l) n), p l) -> (forall (l: list T) (nleq: le (length l) (S n)), p l))
). induction n. split. intros. inversion nleq. apply list_length_0 in H1. rewrite H1. trivial. intros. inversion nleq. set (pn 1). assert  (forall j : list T, le (S (length j)) 1 -> p j). intros. inversion H1. apply list_length_0 in H5. rewrite H5. trivial. inversion H5. set (p1 H1). subst. set (p2 l H2). trivial. subst. inversion nleq. inversion H2. subst. rewrite H5 in H3.   apply list_length_0 in H5. rewrite H5. trivial. subst. inversion H3. apply list_length_0 in H4. rewrite H4. trivial. inversion IHn. clear IHn. set (H0 H). split.  trivial. intros. clear p1. clear H0. inversion nleq. set (pn (S (S n))). assert (forall j : list T, le (S (length j)) (S (S n)) -> p j). subst. intros. rewrite le_S_S in H0. set (H1 j H0). trivial. subst. set (p1 H2 l H3). trivial. subst. set (H1 l H3). trivial. intros. set (H (length l)). inversion a. set (H0 l (le_n (length l))). trivial. Qed.

Theorem head1 {T: Type} (l: list T) (a : ~(length l = 0)): T.
Proof. destruct l. simpl in a. unfold not in a. assert (0 = 0). trivial. set (a H). inversion f. trivial. Qed.

Theorem single_list: forall (T: Type)  (l: list T) (eq: length l = 1), (exists k, l = [k]).
Proof. intros. destruct l. simpl in eq. inversion eq. destruct l. exists t. trivial. simpl in eq. inversion eq. Qed. 


Definition shift: forall (X: Type) (a: X) (b: list X), exists (c: list X) (d: X), a :: b = snoc c d. intros. destruct b. exists []. exists a. trivial. exists (front a (x :: b)). exists (last a (x :: b)). generalize dependent a. generalize dependent x. induction b. trivial. simpl. intros. set (IHb a x). assert (snoc (front x (a :: b)) (last x (a :: b)) = x :: (snoc (front a b) (last a b))). simpl. trivial. rewrite H in e. rewrite e. trivial. Qed.


Theorem snoc_app: forall (X: Type) (f: list X) (a: X), snoc f a = f ++ [a].
Proof. intros. induction f. trivial. simpl. rewrite IHf. trivial. Qed.


Theorem decor_list: forall (T: Type) (l: list T) (len: le 2 (length l)), (exists (a b: T) (j: list T), l = a :: j ++ [b]).
Proof. intros. destruct l. simpl in len. inversion len. destruct l. simpl in len. inversion len. subst. inversion H1. set (shift T t0 l). inversion e.  inversion H. exists t. exists x0. exists x. rewrite H0. rewrite snoc_app. trivial. Qed.


Goal forall (T: Type) (l: list T), @rev T l = l -> pal l.
Proof. intros T. refine ((generalized_list_induction T) (fun (l: list T) => (@rev T l = l -> pal l)) _ _). intros. constructor. intros. destruct n. apply list_length_0 in H0. rewrite H0. constructor. destruct n. set (single_list T l H0). inversion e. rewrite H2. constructor. assert (le 2 (length l)). rewrite H0. apply le_S_S. rewrite le_S_S. apply le_0_n. set (decor_list  T l H2). inversion e. clear e. inversion H3. clear H3. inversion H4. clear H4. assert (le (S (length x1)) (S (S n))). assert ((S ( S (length x1))) = S (S n)). rewrite <- H0. rewrite H3. simpl. rewrite app_length. simpl. rewrite plus_comm. simpl. trivial. apply -> le_S_S. constructor. rewrite H4. constructor. set (H x1 H4). assert (rev x1 = x1). rewrite H3 in H1. simpl in H1. rewrite rev_app_distr in H1. simpl in H1. inversion H1. subst.  assert (rev( rev x1 ++ [x]) = rev (x1 ++ [x])). rewrite H7. trivial. rewrite rev_app_distr in H3. rewrite rev_app_distr in H3. inversion H3. rewrite rev_involutive in H6. symmetry. rewrite rev_involutive. trivial. rewrite H3. assert (x :: x1 ++ [x0]= [x] ++ x1 ++ [x0]). simpl. trivial. rewrite H6. set (H x1 H4 H5). assert (x = x0). rewrite H3 in H1. simpl in H1. rewrite rev_app_distr in H1. simpl in H1. inversion H1. trivial. rewrite H7. constructor. trivial. Qed.





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

Theorem lt_trans_r: forall a b c, a <= b -> b < c -> a < c.
Proof. intros. induction H. trivial. assert (m < c). unfold lt. unfold lt in H0. assert (S m <= S (S m)). constructor. constructor. refine (le_trans _ _ _ H1 H0). apply IHle in H1. trivial. Qed. 

Theorem lt_trans_l: forall a b c, a < b -> b <= c -> a < c.
Proof. intros. induction H0. trivial. unfold lt. constructor. unfold lt in H. refine (le_trans _ _ _ H H0). Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. intros. split. assert (n1 <= n1 + n2). apply le_plus_l. refine (lt_trans_r _ _ _ H0 H). assert (n2 <= n1 + n2). rewrite plus_comm. apply le_plus_l. refine (lt_trans_r _ _ _ H0 H). Qed.


Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof. intros. assert (m <= S m). constructor. constructor. refine (lt_trans_l _ _ _ H H0). Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.  induction n. intros . apply le_0_n. induction m. simpl. intros. inversion H. simpl. intros. apply IHn in H. rewrite le_S_S. trivial. Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof. intros. generalize dependent n. induction m. intros. inversion H. simpl. trivial. intros. induction n. simpl. trivial. rewrite le_S_S in H. apply IHm in H. simpl. trivial. Qed. 

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof. intros. apply ble_nat_true in H. apply ble_nat_true in H0. apply le_ble_nat. refine (le_trans _ _ _ H H0). Qed.

(** **** Exercise: 2 stars, optional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof. induction n. intros. simpl in H. inversion H. induction m. simpl. intros. unfold not. intros. inversion H0. simpl. intros. apply IHn in H. unfold not. intros. rewrite le_S_S in H0. apply H in H0. trivial. Qed.


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

Goal forall a b c, a + b = c -> R a b c.
Proof. intros. rewrite <- H. clear H. generalize dependent a. generalize dependent b. refine (double_induction _ _ _ _ _ ). simpl. constructor. simpl. constructor. trivial. simpl. intros. rewrite (plus_0_r). rewrite plus_0_r in H. constructor. trivial. intros. rewrite plus_Sn_m. rewrite plus_comm. rewrite plus_Sn_m. constructor. constructor. rewrite plus_comm. trivial. Qed.

Require Import Omega Arith List Recdef Program NPeano.



Goal forall a b c, R a b c -> a + b = c.
Proof. intros. induction H. trivial. simpl. rewrite
IHR. trivial. rewrite plus_comm. rewrite plus_Sn_m. rewrite plus_comm. rewrite IHR. trivial. simpl in IHR. rewrite plus_comm in IHR. simpl in IHR. inversion IHR. rewrite plus_comm. trivial. rewrite plus_comm. trivial. Qed.

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

Inductive subseq: (list nat) -> (list nat) -> Prop :=
  | sub_nil: subseq [] []
  | sub_skip: forall  l r e, subseq l r -> subseq l (e :: r)
  | sub_cons: forall l r e, subseq l r -> subseq (e :: l) (e:: r).

Theorem sub_refl: forall l: list nat, (subseq l l).
Proof. induction l. constructor. constructor 3. trivial. Qed.

Theorem cons_to_app: forall T a b, @cons T a b = [a] ++ b.
Proof. intros. simpl. trivial. Qed.

Theorem subseq_nil: forall l, subseq [] l.
Proof. intros. induction l. constructor. constructor. trivial. Qed.

Theorem sub_app: forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof. intros. induction H. apply subseq_nil. rewrite cons_to_app. rewrite <- app_assoc. simpl. constructor. trivial. assert ((e :: r) ++ l3 = e :: r ++ l3). rewrite cons_to_app. rewrite <- app_assoc. simpl. trivial. rewrite H0. clear H0. constructor 3. trivial. Qed.

Require Export Program.

Theorem sub_head: forall a s l, subseq (a :: s) l -> subseq s l.
Proof. intros. dependent induction H. constructor. trivial.  constructor. trivial. Qed.

(* FIXME *)
Theorem sub_trans : forall l1 l2 l3, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof. admit.
Qed.



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

Definition combine_odd_even (Podd Peven : nat -> Prop) n : Prop :=
  if oddb n then Podd n else Peven n.




Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof. intros. unfold combine_odd_even in *. remember (oddb n). destruct b. apply H. trivial. apply H0. trivial. Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof. intros. unfold combine_odd_even in *. rewrite H0 in H. trivial. Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof. intros. unfold combine_odd_even in H. rewrite H0 in H. trivial. Qed.

Fixpoint true_upto_n__true_everywhere (n : nat) (P : nat -> Prop) :=
  match n with
  | O => forall n, P n
  | S N => (P n) -> true_upto_n__true_everywhere N P
  end.


Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => ev n))
  = (ev 3 -> ev 2 -> ev 1 -> forall m : nat, ev m).
  simpl in *.
  trivial.
Qed.

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
Fixpoint true_upto_n__true_everywhere (n : nat) (P : nat -> Prop) { struct n } :=
  match n with
  | O => forall n, P n
  | S N => (P n) -> true_upto_n__true_everywhere N P
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
  simpl in *.
  trivial.
Qed.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

