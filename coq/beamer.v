Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

(* Ejemplo 1 *)
Check le_n_S.
Check le_0_n.

Definition le_S (n : nat) : n <= S n.
Proof.
induction n.
- apply (le_0_n 1).
- apply (le_n_S (n) (S n)). exact IHn.
Qed.

(* Ejemplo 2 *)
Inductive myList (A : Type) : Type :=
| myNil : myList A
| myCons : A -> myList A -> myList A.

Definition head_d {A} (l : myList A) (d : A) : A :=
  match l with
  | myNil _ => d
  | myCons _ x xs => x
  end.

Definition head_o {A} (l : myList A) : option A :=
  match l with
  | myNil _ => None
  | myCons _ x xs => Some x
  end.

Program Definition head {A}
(l : myList A | myNil _ <> l ) : A :=
  match l with
  | myNil _ => !
  | myCons _ x xs => x
  end.