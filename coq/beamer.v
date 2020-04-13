Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

From Mtac2 Require Import Base Mtac2 Specif Sorts MTele MFixDef MTeleMatch MFix.
Import Sorts.S.
Import M.notations.
Import M.M.
From Coq Require Import ssreflect ssrfun ssrbool.

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

(* Mtac2 *)

About bind.
About ret.

Definition arith_eval : nat -> M nat :=
  mfix1 f (n : nat) : M nat :=
    mmatch n with
    | [? y] add O y =>
      y <- f y;
      ret y
    | [? x] add x O =>
      x <- f x;
      ret x
    | [? x y] add x y =>
      x <- f x;
      y <- f y;
      ret (add x y)
    | _ => ret n
  end.

Definition test : nat := ltac:(mrun (arith_eval (3+1))).
Eval compute in test.

(* Motivacion *)

Definition boolMax (b b' : bool) : bool :=
  if b then b else b'.