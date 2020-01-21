Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition add_list {A} (x : A) (l : list A) : list A :=
  cons x l.

Fixpoint len {A} (l : list A) : nat :=
match l with
| [] => O
| x :: xs => S (len xs)
end.

Eval compute in length [1;2;3].

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