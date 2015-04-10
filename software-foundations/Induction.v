
Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem andb_true_elim1: forall b c: bool, andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  reflexivity.
  rewrite <- H.
  reflexivity.
Qed.


(** i have no idea it works with destruct **)

Theorem plus_0_r: forall n : nat, n + 0 = n.
Proof. intros n. induction n as [|n']. reflexivity. simpl. rewrite -> IHn'. reflexivity.

Theorem mult_0_r: forall n: nat, n * 0 = 0.
Proof. intros n. induction n as [| n']. 
reflexivity. simpl. rewrite IHn'. reflexivity. Qed.

Theorem plus_n_Sm: forall n m: nat, S (n + m) = n + (S m).
Proof.  induction n as [|k]. induction m as [|k]. simpl. reflexivity. simpl. reflexivity. simpl. intros m. rewrite IHk. reflexivity. Qed.

Theorem plus_comm: forall n m: nat, m + n = n + m.
Proof. intros n. induction m as [|k]. rewrite <- plus_n_O. simpl. reflexivity. simpl. rewrite IHk. rewrite plus_n_Sm. reflexivity. Qed.

Theorem plus_assoc: forall n m p: nat, n + (m + p) = (n + m) + p.
Proof. induction n as [|k]. simpl. reflexivity.  simpl. intros m p. rewrite IHk. reflexivity. Qed.

Fixpoint double (n: nat) := 
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
  
Lemma double_plus: forall n, double n = n + n.
Proof. intros n. induction n as [|k].
 reflexivity. simpl. rewrite IHk. rewrite <- plus_Sn_m. rewrite plus_comm. reflexivity. Qed.
 
Theorem plus_swap: forall n m p: nat, 
n + (m + p) = m + (n + p).
Proof. intros n m p. rewrite plus_assoc. rewrite plus_assoc. assert (n + m = m + n). rewrite plus_comm. reflexivity. rewrite H. reflexivity. Qed.

Check mult.

Theorem mult_lemma: forall m n: nat, m * S n = m * n + m.
Proof. induction m as [|k]. reflexivity. simpl. intros n. rewrite IHk. simpl. rewrite <- plus_Sn_m. rewrite plus_swap. assert (k * n + n = n + k * n). rewrite plus_comm. reflexivity. rewrite <- H.   assert (S n + k = n + S k).  assert (n + S k = S k + n). rewrite plus_comm. reflexivity. rewrite H0. simpl. rewrite plus_comm. reflexivity. rewrite H0. rewrite plus_assoc. reflexivity.
Qed.



Theorem mult_comm: forall m n: nat, m * n = n * m.
Proof. induction n as [|k].  rewrite mult_0_r. simpl. reflexivity. simpl. rewrite <- IHk.  rewrite plus_comm. rewrite mult_lemma. reflexivity. Qed.


Fixpoint evenb(n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb(n')
  end.
  
Definition oddb(n: nat) : bool := negb(evenb n).

Theorem evenb_n__oddb_Sn: forall n: nat, evenb n = negb(evenb (S n)).
Proof. intros n. simpl.  induction n as [|k]. simpl. reflexivity. simpl. rewrite IHk. simpl. assert (forall k: bool, negb (negb k) = k). intros k0. destruct k0. reflexivity. reflexivity. rewrite H. simpl. reflexivity. Qed.









