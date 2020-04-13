Require Import Program.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Logic.Decidable.

From Mtac2 Require Import Base Mtac2 Specif Sorts MTele MFixDef MTeleMatch MFix.
Import Sorts.S.
Import M.notations.
Import M.M.
From Coq Require Import ssreflect ssrfun ssrbool.

About t.
Check add.

Definition test_match (n : nat) : M nat :=
mmatch n with
| [? x y] add x y => ret n
| O => ret (S O)
| [? n']S n' => ret (S (S n'))
end.

Eval compute in test_match 1.

Definition map {A} {B} (t : A -> B) : forall (l : list A), M (list B) :=
  mfix1 m (l : list A) : M list B :=
    mmatch l with
    | nil => ret nil
    | [? x xs] x::xs => xs' <- m xs;
                       ret ((t x)::xs')
    end.

Definition nmon : (1 + 1 = 2).
Proof.
reflexivity.
Qed.

Print nmon.

Definition MyException : Exception. exact exception. Qed.

Definition wmon : M (1 + 1 = 2) :=
  raise MyException.

Definition univ (P : Prop): M P :=
  raise MyException.

Print app.
About nil_cons.

Lemma app_not_nil: forall {A} (l1 l2 : list A), (app l1 l2) <> nil -> (l1 <> nil) + (l2 <> nil).
Proof.
move=> A l1 l2. case: l1.
- simpl. move=> H. by apply inr.
- simpl. move=> x l' _. apply inl,not_eq_sym,nil_cons.
Defined.

About bind.
(*
Definition list_max_nat :=
  mfix f (l: list nat) : l <> nil -> M nat :=
    mtmmatch l as l' return l' <> nil -> M nat with
    | [? e] [e] =m> fun P => M.ret e
    | [? e1 e2 l'] (e1 :: e2 :: l') =m> fun P =>
      let x := Nat.max e1 e2 in
      f (x :: l') _
    | [? l' r'] app l' r' =m> fun P =>
      match app_not_nil l' r' P with
      | inl P' => f l' P'
      | inr P' => f r' P'
      end
    end.

Definition boolMax (b b' : bool) : bool :=
  if b then b else b'.

Definition max (S: Set) : M (S -> S -> S) :=
  mmatch S in Set as S' return M (S' -> S' -> S') with
  | nat => M.ret Nat.max
  end.

Definition list_max (S: Set)  :=
  max <- max S; (* error! *)
  mfix f (l: list S) : l' <> nil -> M S :=
    mtmmatch l as l' return l' <> nil -> M S with
    | [? e] [e] =m> fun nonE=>M.ret e
    | [? e1 e2 l'] (e1 :: e2 :: l') =m> fun nonE =>
      m <- max e1 e2;
      f (m :: l') _
    end.

*)

Definition m : MTele := mTele (fun T : Type => mTele (fun l : list T =>  mTele (fun p : List.length l = 0 => mBase))).

Eval cbn in MTele_Ty m.

Definition tm : MTele_Ty m := fun T l p => l = nil.

About MTele_val.
Eval cbn in MTele_val tm.

Print Datatypes.length.

Definition test_m : forall T (l : list T) (p : List.length l = 0), l = nil.
intros T l p. by apply length_zero_iff_nil.
Qed.

Definition vm : MTele_val tm := test_m.
