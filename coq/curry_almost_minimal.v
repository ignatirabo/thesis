From Mtac2 Require Import Base Mtac2 Specif Sorts MTele MFixDef MTeleMatch.
Require Import Coq.Lists.List.
Import Sorts.S.
Import M.notations.
Import M.M.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Unset Printing Universes.

Local Definition MFA {n} (T : MTele_Ty n) := (MTele_val (MTele_C Type_sort Prop_sort M T)).
Local Notation InF s n := (forall now_ty : forall s0 : Sort, MTele_Sort s0 n -> s0, (forall (s0 : Sort) (T : MTele_Sort s0 n), MTele_val T -> now_ty s0 T) -> s).

(* If recursion is needed then it's TyTree, if not only Type *)
Inductive TyTree : Type :=
| tyTree_val {m : MTele} (T : MTele_Ty m) : TyTree
| tyTree_M (T : Type) : TyTree
| tyTree_MFA {m : MTele} (T : MTele_Ty m) : TyTree
| tyTree_In (s : Sort) {m : MTele} (F : accessor m -> s) : TyTree
| tyTree_imp (T : TyTree) (R : TyTree) : TyTree
| tyTree_FATeleVal {m : MTele} (T : MTele_Ty m) (F : MTele_val T -> TyTree) : TyTree
| tyTree_FATeleType (m : MTele) (F : MTele_Ty m -> TyTree) : TyTree
| tyTree_FAVal (T : Type) (F : T -> TyTree) : TyTree
| tyTree_FAType (F : Type -> TyTree) : TyTree
| tyTree_base (T : Type) : TyTree
.

Fixpoint to_ty (X : TyTree) : Type :=
  match X as X' with
  | tyTree_val T => MTele_val T
  | tyTree_M T => M T
  | tyTree_MFA T => MFA T
  | tyTree_In s F => MTele_val (MTele_In s F)
  | tyTree_imp T R => to_ty T -> to_ty R
  | @tyTree_FATeleVal m T F => forall T, to_ty (F T)
  | tyTree_FATeleType m F => forall T : (MTele_Ty m), to_ty (F T)
  | tyTree_FAVal T F => forall t : T, to_ty (F t)
  | tyTree_FAType F => forall T : Type, to_ty (F T)
  | tyTree_base T => T
  end.


Definition to_tree (X : Type) : M TyTree :=
  (mfix1 rec (X : Type) : M TyTree :=
    mmatch X as X return M TyTree with
    | [? T : Type] (M T):Type =>
      ret (tyTree_M T)
    | [? T R : Type] T -> R => (* no dependency of T on R. It's equivalent to forall _ : T, R *)
      T <- rec T;
      R <- rec R;
      ret (tyTree_imp T R)
    | [? F : Type -> Type] forall T : Type, F T =>
      \nu T : Type,
        F <- rec (F T);
        F <- abs_fun T F;
        ret (tyTree_FAType F)
    | [? T (F : forall t : T, Type)] forall t : T, F t =>
      \nu t : T,
        F <- rec (F t);
        F <- abs_fun t F;
        ret (tyTree_FAVal T F)
    | _ => ret (tyTree_base X)
    (* | [? (m : MTele) (T : MTele_Ty m)] MTele_val T =>
       ret (tyTree_val p T) (* fail *) *)
    (* | [? (m : MTele) (T : MTele_Ty m)] (MFA T):Type =>
      ret (tyTree_MFA T) (* fail *) *)
    (* | [? (m : MTele) (T : MTele_Ty m) (F : forall x : MTele_val T, Type)] forall T , F T =>
      \nu t : _,
        F <- rec (F t) p;
        F <- abs_fun t F;
        ret (tyTree_FATeleVal p T F) (* fail *) *)
    end) X.

(*** Is-M *)

(* Checks if a given type A is found "under M" *)
(* true iff A is "under M", false otherwise *)
Definition is_m (T : TyTree) (A : Type) : M bool :=
  print "is_m on T:";;
  print_term T;;
  (mfix1 f (T : TyTree) : M bool :=
  mmatch T return M bool with
  | [? X] tyTree_base X => ret false
  | [? X] tyTree_M X =>
    mmatch X return M bool with
    | A => ret true
    | _ => ret false
    end
  | [? X Y] tyTree_imp X Y =>
    fX <- f X;
    fY <- f Y;
    let r := orb fX fY in
    ret r
  | [? F] tyTree_FAType F =>
    print_term (F A);;
    \nu X : Type,
    f (F X)
  | [? X F] tyTree_FAVal X F =>
    \nu x : X,
      f (F x)
  | _ => ret false
  end) T.

(* This function is used to determine if a TyTree contains a mention of an element U *)
(* The idea is to abstract and if the abstraction fails, it means that U is in T *)
(* It's a hack Janno figured we could use *)
Definition contains_u (m : MTele) (U : ArgsOf m) (T : TyTree) : M bool :=
  mtry
    T' <- abs_fun U T;
    print "T' on contains_u:";;
    print_term T';;
    mmatch T' with
    | [? T''] (fun _ => T'') =>
      ret false
    | _ =>
      ret true
    end
  with AbsDependencyError =>
    ret true
  end.

(*** Lift In section *)

Fixpoint uncurry_val {s : Sort} {m : MTele} :
  forall {A : MTele_Sort s m},
  MTele_val A -> forall U : ArgsOf m, @apply_sort s m A U :=
  match m as m return
        forall A : MTele_Sort s m,
          MTele_val A -> forall U : ArgsOf m, @apply_sort s m A U
  with
  | mBase => fun A F _ => F
  | mTele f => fun A F '(mexistT _ x U) => @uncurry_val s (f x) _ (App F x) _
  end.

Definition uncurry_in_acc {m : MTele} (U : ArgsOf m) : accessor m :=
  let now_const := fun (s : Sort) (T : s) (ms : MTele_Const T m) => apply_const ms U in
  let now_val := fun (s : Sort) (ms : MTele_Sort s m) (mv : MTele_val ms) => uncurry_val mv U in
  Accessor _ now_const now_val.

Definition uncurry_in {s : Sort} :
  forall {m : MTele} (F : accessor m -> s),
  (MTele_val (MTele_In s F)) ->
  forall U : ArgsOf m,
    F (uncurry_in_acc U).
  fix IH 1; destruct m; intros.
  + simpl in *. assumption.
  + simpl in *. destruct U. specialize (IH (F x) _ (App X0 x) a). assumption.
Defined.

Definition UnLiftInCase : Exception. exact exception. Qed.

(* Return: big f with accesors and F now_ty now_ty = to_ty T. *)
(*
Let now_ty {m} (U : ArgsOf m) := fun (s' : Sort) (ms : MTele_Sort s' m) => apply_sort ms U.
Let now_val {m} (U : ArgsOf m) :=
  fun (s' : Sort) (ms : MTele_Sort s' m) (mv : MTele_val ms) => uncurry_val mv U.
*)

(* This is a new type that helps organize the code *)
(* I don't know if there is some kind of intuition *)
Definition lift_inR {m} (T : TyTree) (A : accessor m):=
  m:{F : (accessor m -> Type_sort) & (to_ty T = F A)}.


(* This function is an auxiliary function called by lift. It is only used for tyTree_imp *)
Definition lift_in {m : MTele} (U : ArgsOf m) (T : TyTree) :
                 M (lift_inR T (uncurry_in_acc U)) :=
  (mfix1 f (T : TyTree) : M (lift_inR T (uncurry_in_acc U)) :=
    mmatch T as e return M (lift_inR e _) with
    | [? (A : MTele_Ty m)] tyTree_base (apply_sort A U) =>
      print "lift_in: base";;
      let F : (accessor m -> Type) := fun a => a.(acc_sort) A in
      let eq_p : to_ty (tyTree_base (apply_sort A U)) = F (uncurry_in_acc U) := eq_refl in
      ret (mexistT _ F eq_p)
    | [? (A : MTele_Ty m)] tyTree_M (apply_sort A U) =>
      print "lift_in: M";;
      let F : (accessor m -> Type) := fun a => M (a.(acc_sort) A) in
      let eq_p : to_ty (tyTree_M (apply_sort A U)) = F (uncurry_in_acc U) := eq_refl in
      ret (mexistT _ F eq_p)
    | [? X Y] tyTree_imp X Y =>
      print "lift_in: imp";;
      '(mexistT _ FX pX) <- f X;
      '(mexistT _ FY pY) <- f Y;
      let F := fun a => FX a -> FY a in
      let eq_p : to_ty (tyTree_imp X Y) = F (uncurry_in_acc U) :=
        ltac:(simpl in *; rewrite pX, pY; refine eq_refl) in
      ret (mexistT _ F eq_p)
    | _ => raise UnLiftInCase
    end) T.

(*** Lift section *)

Fixpoint MTele_Cs {s : Sort} (n : MTele) (T : s) : MTele_Sort s n :=
  match n as n return MTele_Sort s n with
  | mBase =>
    T
  | @mTele X F =>
    fun x : X => @MTele_Cs s (F x) T
  end.

Fixpoint MTele_cs {s : Sort} {n : MTele} {X : Type} (f : M X) : MFA (@MTele_Cs Type_sort n X) :=
  match n as n return MFA (@MTele_Cs Type_sort n X) with
  | mBase =>
    f
  | @mTele Y F =>
    (* Fun (fun x : X => @MTele_cs _ (F x) _ f) *)
    @Fun Type_sort Y (fun y : Y => MFA (@MTele_Cs Type_sort (F y) X)) (fun y : Y => @MTele_cs s (F y) X f)
    (* ltac:(simpl in *; refine (@Fun s X (fun x => MTele_val (@MTele_Cs _ (F x) T)) (fun x : X => @MTele_cs _ (F x) T f))) *)
  end.

(* Next line needs to after MTele_cs, if not, Coq fails to typecheck *)
Arguments MTele_Cs {s} {n} _.

Definition ShitHappens : Exception. exact exception. Qed.

Polymorphic Fixpoint lift (m : MTele) (U : ArgsOf m) (T : TyTree) :
  forall (f : to_ty T), M m:{ T : TyTree & to_ty T} :=
  match T as T return forall (f : to_ty T), M m:{ T' : TyTree & to_ty T'} with
  | tyTree_base X =>
    fun f =>
      print "lift: base";;
      ret (mexistT (fun Y : TyTree => to_ty Y) (tyTree_base X) f)
  | tyTree_M X =>
    fun f =>
      print "lift: M";;
      mmatch mexistT (fun X : Type => to_ty (tyTree_M X)) X f
      return M m:{ T' : TyTree & to_ty T'} with
      | [? (A : MTele_Ty m) f]
        mexistT (fun X : Type => to_ty (tyTree_M X))
                (apply_sort A U)
                f =>
          print "T:";;
          print_term (to_ty T);;
          print "f:";;
          print_term f;;
          f <- @abs_fun (ArgsOf m) (fun U => to_ty (tyTree_M (apply_sort A U))) U f;
          print "survive2";;
          let f := curry f in
          ret (mexistT _ (tyTree_MFA A) f)
      | _ =>
        (* Constant case *)
        let T := @MTele_Cs Type_sort m X in (* okay *)
        let f' := @MTele_cs Type_sort m X f in
        ret (mexistT (fun X : TyTree => to_ty X) (tyTree_MFA T) f')
      end
  | tyTree_imp X Y =>
    (* print "hola";; *)
    fun f =>
      print "lift: imp";;
      print "X on imp:";;
      print_term X;;
      b <- contains_u m U X;
      print "b on imp:";;
      print_term b;;
      if b then
        mtry
          ('(mexistT _ F e) <- lift_in U X;
          \nu x : MTele_val (MTele_In Type_sort F),
            (* ltac:(rewrite e in f; exact (f (uncurry_in (s:=SType) F x U))) *)
            (* lift on right side Y *)
            let G := (F (uncurry_in_acc U)) -> to_ty Y in
            match eq_sym e in _ = T return (T -> to_ty Y) -> M _ with
            | eq_refl => fun f =>
              '(mexistT _ Y' f) <- lift m U (Y) (f (uncurry_in (s:=Type_sort) F x U));
              f <- abs_fun x f;
              print "survive1";;
              ret (mexistT to_ty
                  (tyTree_imp (tyTree_In Type_sort F) Y')
                  f)
            end f)
        with UnLiftInCase =>
          mfail "UnLiftInCase raised"
        end
      else
        (* Because X does not contain monadic stuff it's assumed it's "final" *)
        \nu x : to_ty X,
          '(mexistT _ Y' f) <- lift m U (Y) (f x);
          f <- abs_fun x f;
          ret (mexistT to_ty (tyTree_imp X Y') f)
  | tyTree_FAVal X F =>
    fun f =>
      print "lift: FA";;
      \nu x : X,
       '(mexistT _ F f) <- lift m U (F x) (f x);
       F <- abs_fun x F;
       f <- coerce f;
       f <- abs_fun x f;
       ret (mexistT _ (tyTree_FAVal X F) (f))
  | tyTree_FAType F =>
    fun f =>
      print "lift: FAType";;
      \nu A : Type,
      b <- is_m (F A) A;
      if b then (* Replace A with a (RETURN A U) *)
        \nu A : MTele_Ty m,
          (* I use apply_sort A U to uncurry the values *)
          (* 101101000001110apply_sort A U is just forall x y z, A z x y *)
          s <- lift m U (F (apply_sort A U)) (f (apply_sort A U));
          let '(mexistT _ T' f') := s in
          T'' <- abs_fun (P := fun A => TyTree) A T';
          f' <- coerce f';
          f'' <- abs_fun (P := fun A => to_ty (T'' A)) A f';
          let T'' := tyTree_FATeleType m T'' in
          print "T'':";;
          print_term (to_ty T'');;
          print "f'':";;
          print_term f'';;
          ret (mexistT to_ty T'' f'')
      else (* A is not monadic, no replacement *)
        s <- lift m U (F A) (f A);
        let '(mexistT _ T' f') := s in
        T'' <- abs_fun (P := fun A => TyTree) A T';
        f' <- coerce f';
        f'' <- abs_fun (P := fun A => to_ty (T'' A)) A f';
        let T'' := tyTree_FAType T'' in
        print "T'':";;
        print_term T'';;
        print "f'':";;
        print_term f'';;
        ret (mexistT to_ty T'' f'')
  | _ => fun _ =>
    print_term T;;
    raise ShitHappens
  end.

Fixpoint checker (pol : bool) (l : bool) (X : TyTree) : Prop :=
  match X as X' with
  (* direct telescope cases *)
  | tyTree_val T => False
  | tyTree_MFA T => False
  | tyTree_In s F => False
  | @tyTree_FATeleVal m T F => False
  | tyTree_FATeleType m F => False
  (* non-telescope cases *)
  | tyTree_M T =>
    match andb pol l with
    | true => True
    | false => True
    end
  | tyTree_base T => True
  (* indirect cases *)
  | tyTree_imp T R => and (checker (negb pol) true T) (checker pol false R)
  | tyTree_FAVal T F => forall t : T, checker pol false (F t)
  | tyTree_FAType F => forall T : Type, checker pol false (F T)
  end.

Definition NotProperType : Exception. exact exception. Qed.

Definition checker' : forall (p : bool) (l : bool) (T : TyTree), M (checker p l T) :=
  mfix3 f (p : bool) (l : bool) (T : TyTree) : M (checker p l T) :=
    mmatch T as T' return M (checker p l T') with
    | [? X] tyTree_base X => ret (I)
    | [? X] tyTree_M X =>
      match p as p' return M (checker p' l (tyTree_M X)) with
      | true =>
        match l as l' return M (checker true l' (tyTree_M X)) with
        | true => ret I
        | false => ret (I)
        end
      | false => ret (I)
      end
    | [? (F : Type -> TyTree)] tyTree_FAType F =>
      \nu X : Type,
        t <- f p false (F X);
        t <- abs_fun (P := fun X : Type => checker p false (F X)) X t;
        ret (t)
    | [? (X : Type) (F : X -> TyTree)] tyTree_FAVal X F =>
      \nu x : X,
        t <- f p false (F x);
        t <- abs_fun (P := fun x : X => checker p false (F x)) x t;
        ret (t)
    | [? (X Y : TyTree)] tyTree_imp X Y =>
      x <- f (negb p) true X;
      y <- f p false Y;
      ret (conj x y)
    | _ => raise NotProperType
    end.

Definition lift' {T : TyTree} (f : to_ty T) : MTele -> M m:{T : TyTree & to_ty T} :=
  fun (m : MTele) =>
  \nu U : ArgsOf m,
    c <- (checker' true false T);
    lift m U T f.

(** Everything works! *)

(** ret *)
(* This is related to the motivation *)
Let R := tyTree_FAType (fun A : Type => (tyTree_imp (tyTree_base A) (tyTree_M A))).
Let r : to_ty R := @ret.

Definition l_ret (m : MTele): m:{T : TyTree & to_ty T} := ltac:(mrun (lift' r m)).


Definition m_fun := fun (T : Type) (l : list T) => mTele (fun p : l <> nil => mBase).

Definition l : list nat := cons 3 (cons 1 (cons 10 (cons 7 nil))).

Lemma l_nil : l <> nil.
Proof.
unfold l. unfold not. intros H. apply eq_sym in H. apply nil_cons in H. apply H.
Qed.

Definition m := m_fun nat l.
Eval cbn in ArgsOf m.
Definition U : ArgsOf m := mexistT _ l_nil tt.

About r.
Definition li_ret : m:{T : TyTree & to_ty T} := ltac:(mrun (lift m U R r)).

Eval cbn in fun T l => to_ty (mprojT1 (l_ret (tele_motiv_fun T l))).
Eval cbn in to_ty (mprojT1 (l_ret (tele_motiv))).

Eval cbn in fun T l => (mprojT2 (l_ret (tele_motiv_fun T l))).
Eval cbn in mprojT2 (l_ret (tele_motiv)).

Eval cbn in fun T l => (mprojT1 (l_ret (tele_motiv T l))).