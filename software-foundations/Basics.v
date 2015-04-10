

Inductive day: Type :=
  | monday: day
  | tuesday: day
  | wednesday: day
  | thursday: day
  | friday: day
  | saturday: day
  | sunday: day.

Print day.

Definition next_weekday (d:day) :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.
  
Print next_weekday.


Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true: bool
  | false: bool.
  
Definition negb(b: bool) := match b with
  | true => false
  | false => true
  end.
  
Definition andb(b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
  
Definition orb(b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
  

Definition nandb (b1: bool) (b2: bool) : bool :=
  negb (andb b1 b2).
  
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1: bool) (b2: bool) (b3: bool) := andb b1 (andb b2 b3).

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.

Print true.

Check (negb true).

Check negb.


Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
  
Definition pred (n: nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End Playground1.

Check (S (S O)).

Check S.

Fixpoint evenb(n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb(n')
  end.
  
Definition oddb(n: nat) : bool := negb(evenb n).

Module Playground2.

Fixpoint plus (n: nat) (m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
  
Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m: nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus(n m: nat) := 
  match n, m with
  | O, _ => O
  | S n1, S n2 => minus n1 n2
  | a, O => a
  end.

End Playground2.

Fixpoint exp(base power: nat) :=
  match power with
  | O => S O
  | S n => mult (exp base n) base
  end.

Fixpoint factorial (n: nat) :=
  match n with
  | O => S O
  | S n => mult (S n) (factorial n)
  end.
  
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.

Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.

Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Fixpoint beq_nat (n m: nat) :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S m, S n => beq_nat m n
  end.
  
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.
  
Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.


Definition blt_nat (m n: nat) : bool := andb (ble_nat m n) (negb (beq_nat m n)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n: nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example: forall n m: nat, n = m -> n + n = m + m.
Proof. intros m n. intros H. rewrite -> H. reflexivity. Qed.


Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H1. intros H2. rewrite -> H1. rewrite -> H2. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.



Theorem plus_n_O: forall n: nat, n + 0 = n.
Proof. intros n. destruct n as [| n'].  reflexivity. simpl. rewrite  <- plus_n_O. simpl. reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 (n + 1) = false.
Proof. intros n. destruct n as [| n']. reflexivity. reflexivity. Qed.

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof. intros f. intros H. destruct b. rewrite H. rewrite H. reflexivity. rewrite H. rewrite H. reflexivity. Qed.

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. intros b c. destruct b. simpl. intros H. rewrite H. reflexivity. simpl. intros H. rewrite H. reflexivity. Qed.

(** i must say that this bin is
ill posed, twice zero != zero, the thing is you might not use the actual inductive type at all, but you need to use the functions with them, then you can insure that it is well posed **)

Inductive bin : Type :=
  | zero: bin
  | twice: bin -> bin
  | twiceAndOne: bin -> bin.

Fixpoint normalize (b: bin) :bin :=
  match b with
  | zero => zero
  | twiceAndOne c => twiceAndOne c
  | twice d =>
    match (normalize d) with
    | zero => zero
    | a => twice a
    end
  end.
  
Eval compute in (normalize (twice (twice zero))).

Fixpoint incr (b: bin) : bin :=
  match b with
  | zero => twiceAndOne zero
  | twice a => twiceAndOne a
  | twiceAndOne b => twice (incr b)
  end.
  
Fixpoint bin_to_nat (b: bin) : nat :=
  match b with
  | zero => 0
  | twice c => (bin_to_nat c) * 2
  | twiceAndOne c => 2 * (bin_to_nat c) + 1
  end.
  

Example test_bin_incr1: (bin_to_nat (incr (incr (twice (twiceAndOne (twiceAndOne zero)))))) = 8.
Proof. reflexivity. Qed.

Example test_bin_incr2: (bin_to_nat (incr (incr (twiceAndOne (twiceAndOne (twiceAndOne zero)))))) = 9.
Proof. reflexivity. Qed.


(** the example is normalize then incr **)










