Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

From Mtac2 Require Import Base Mtac2 Specif Sorts MTele MFixDef MTeleMatch.
Import Sorts.S.
Import M.notations.
Import M.M.

About t.

Definition add_list {A} (x : A) (l : list A) : list A :=
  cons x l.

Fixpoint len {A} (l : list A) : nat :=
match l with
| [] => O
| x :: xs => S (len xs)
end.

Definition lent {A} (l : list A) : nat.
Proof.
induction l.
- exact O.
- exact (S IHl).
Qed.

Definition head_d {A} (l : list A) (d : A) : A :=
  match l with
  | [] => d
  | x :: xs => x
  end.

Definition head_o {A} (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => Some x
  end.

Program Definition head {A}
(l : list A | [] <> l ) : A :=
  match l with
  | [] => !
  | x :: xs => x
  end.

Eval compute in head (exist _ (2 :: []) (@nil_cons nat 2 [])).

Print Is_true.
Check add.

Definition test_match (n : nat) : M nat :=
mmatch n with
| [? x y] add x y => ret n
| O => ret (S O)
| [? n']S n' => ret (S (S n'))
end.

Eval compute in test_match 1.

Definition map {A} {B} (t : A -> B) : forall (l : list A), list B :=
mfix1 m (l : list A) : list B :=
_.