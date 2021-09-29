Require Export BuildTac.
Require Import Extension.


Set Implicit Arguments.

Unset Strict Implicit.

Parameter eps : R.
Hypothesis eps_pos : (0 <= eps)%R.

Inductive Ut : Type := 
| Point
| Set_of_Points.
 
Inductive uop : Type :=
| Oremove
| Oadd
| Ocompl.

Inductive usupport_ (T_type:Type) (T_Nat:T_type) (T_User:Ut -> T_type) 
 (E_expr:T_type -> Type) (T_Prod : T_type -> T_type) 
 (T_List : T_type -> T_type): T_type -> Type :=
 | choose_points : forall (D F X1 X2:E_expr (T_User Set_of_Points)),
   @usupport_ _ T_Nat T_User E_expr T_Prod T_List (T_Prod (T_User Point))
 | choose_index: forall (D:E_expr (T_User Set_of_Points)) 
    (F: E_expr (T_List (T_User Set_of_Points))) (N:E_expr T_Nat),
   @usupport_ _ T_Nat T_User E_expr T_Prod T_List (T_Nat).


Module Sem (MS:FiniteQuasiMetricSpace) <: SEM.

 Module MSC := QMetricExtension (MS).
 Export MSC.

 Parameter dummy : E.t.

 (** * User-defined type module *)
 Module UT <: UTYPE.

  Definition t := Ut. 

  Definition eqb (x y:t) :=
   match x, y with
   | Point, Point => true
   | Set_of_Points, Set_of_Points => true
   | _,_ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros x y; case x; case y; simpl; trivial; discriminate.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True} :=
   match x as x0 return {x0 = y} + {True} with
   | Point => 
     match y as y0 return {Point = y0} + {True} with 
     | Point => left _ (refl_equal _) 
     | _ => right _ I
     end
   | Set_of_Points => 
     match y as y0 return {Set_of_Points = y0} + {True} with 
     | Set_of_Points => left _ (refl_equal _) 
     | _ => right _ I
     end  
  end.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   intros x y; case x; case y; simpl; intros; discriminate.
  Qed.

  Definition interp (k:nat) (t0:t) : Type := 
   match t0 with
   | Point => E.t
   | Set_of_Points => Set_of_E.t 
   end.

  Definition size k (t0:t) (_:interp k t0) := S O.

  Definition default k (t0:t) : interp k t0.
   intros; destruct t0; simpl.
     exact dummy.
     exact Set_of_E.empty.
  Defined.

  Definition default_poly (t0:t) := pcst 1.

  Lemma size_positive : forall k t0 (x:interp k t0), (0 < size x)%nat.
  Proof.
   intros k t0 x.
   unfold size; auto with arith.
  Qed.

  Lemma default_poly_spec : forall k (t0:t),
   (size (default k t0) <= peval (default_poly t0) k)%nat.
  Proof.
   intros k t0.
   unfold size, default, default_poly.
   rewrite pcst_spec; trivial.
  Qed.

  Definition i_eqb k t : interp k t -> interp k t -> bool :=
   match t with 
   | Point => fun x1 x2 =>  if E.eq_dec x1 x2 then true else false
   | Set_of_Points => fun X1 X2 => if Set_of_E_eqb X1 X2 then true else false
   end.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros; unfold i_eqb.
   destruct t0.
     destruct (E.eq_dec x y); trivial.
     generalize (Set_of_E_eqb_spec x y).
     destruct (Set_of_E_eqb x y); simpl; trivial.
  Qed.

 End UT.

 Module T := MakeType UT.


 (** * Module for user-defined operators *)
 Module Uop <: UOP UT T.

  Definition t := uop.

  Definition eqb (o1 o2:t) : bool :=
   match o1, o2 with
    | Oremove, Oremove => true
    | Oadd, Oadd => true
    | Ocompl, Ocompl => true
    | _, _ => false
   end.

  Lemma eqb_spec :  forall x y, if eqb x y then x = y else x <> y.
  Proof.
   destruct x; destruct y; simpl; trivial; intro; discriminate.
  Qed.

  Definition targs (op : t) : list T.type :=
   match op with
    | Oremove => T.User Set_of_Points :: T.User Point :: nil
    | Oadd =>  T.User Set_of_Points :: T.User Point :: nil 
    | Ocompl => T.User Set_of_Points :: nil
   end.

  Definition tres (op: t) : T.type :=
   match op with
    | Oremove =>  T.User Set_of_Points 
    | Oadd =>  T.User Set_of_Points 
    | Ocompl =>  T.User Set_of_Points 
   end.

  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
    | Oremove => fun X p => Set_of_E.remove p X
    | Oadd => fun X p => Set_of_E.add p X
    | Ocompl => compl
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
    | Oremove => fun X p => (Set_of_E.remove p X, O) 
    | Oadd => fun X p => (Set_of_E.add p X, O)
    | Ocompl => fun X => (compl X, O)
   end.

  Implicit Arguments cinterp_op [k].

  Definition eval_op k
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
   @T.app_op k (targs op) (tres op) (interp_op op) args.

  Definition ceval_op k 
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
   @T.capp_op k (targs op) (tres op) (cinterp_op op) args.

  Lemma ceval_op_spec : forall k op args,
   @eval_op k op args = fst (@ceval_op k op args).
  Proof.
   intros k o args; destruct o; simpl in args;
    T.dlist_inversion args; subst; trivial.
  Qed.

 End Uop.


 Module Var := MakeVar UT T.

 Module Proc := MakeProc UT T.

 Module O := MakeOp UT T Uop.

 Module Mem := MakeMem UT T Var.

 Module E := MakeExpr UT T Var Mem Uop O.

 Open Scope R_scope.

 Module US <: USUPPORT UT T Var Mem Uop O E.

  Module VarP := MkEqBool_Leibniz_Theory Var.
  Module Vset := MkListSet VarP.Edec.


  Definition usupport := usupport_ T.Nat T.User E.expr 
    (fun T => T.Pair T T) (fun T => T.List T).

  Definition eval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) :=
   match s with
     | choose_points D F X1 X2 => pick_points (E.eval_expr D m)
       (E.eval_expr F m) (E.eval_expr X1 m) (E.eval_expr X2 m) eps
     | choose_index D F N => pick_index (E.eval_expr D m)
       (fun i => List.nth i (E.eval_expr F m) Set_of_E.empty) (E.eval_expr N m) eps
   end.

  Definition ceval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) * nat :=
   match s with
    | choose_points D F X1 X2 => (pick_points (E.eval_expr D m)
       (E.eval_expr F m) (E.eval_expr X1 m) (E.eval_expr X2 m) eps, S O)
    | choose_index D F N => (pick_index (E.eval_expr D m)
       (fun i => List.nth i (E.eval_expr F m) Set_of_E.empty) (E.eval_expr N m) eps, S O)
   end.

  Lemma ceval_spec : forall k t (s:usupport t) (m:Mem.t k), 
   eval s m = fst (ceval s m).
  Proof.
   intros; case s; intros; simpl; trivial.
  Qed.   

  (** TODO:Add to EXPR *)
  Variable fv_expr : forall t (e:E.expr t), Vset.t.

  Let req_mem k X (m1 m2:Mem.t k) := 
   forall t (x:Var.var t), Vset.mem x X -> m1 x = m2 x.

  Lemma req_mem_weaken : forall k X X',
   Vset.subset X X' -> forall (m m':Mem.t k), req_mem X' m m' -> req_mem X m m'.
  Proof.
   unfold req_mem; intros; eauto using Vset.subset_correct.
  Qed.

  Let depend_only_distr (X:Vset.t) t (s:usupport t) :=
   forall k (m1 m2:Mem.t k), 
    req_mem X m1 m2 -> eval s m1 = eval s m2.

  Let depend_only (X:Vset.t) t (e:E.expr t) := 
   forall k (m1 m2:Mem.t k), req_mem X m1 m2 -> E.eval_expr e m1 = E.eval_expr e m2.

  Axiom depend_only_fv_expr : forall t (e:E.expr t), 
   depend_only (fv_expr e) e.

  Definition fv_distr t (s:usupport t) : Vset.t :=
   match s with
     | choose_points D F X1 X2 => Vset.union (fv_expr D) (Vset.union (fv_expr F) 
       (Vset.union (fv_expr X1) (fv_expr X2)))
     | choose_index D F N =>  Vset.union (fv_expr D) (Vset.union (fv_expr F) 
       (fv_expr N))
   end.

  Module VsetP := MkSet_Theory Vset.
  
  Lemma depend_only_fv_distr : forall t (s:usupport t), 
   depend_only_distr (fv_distr s) s.
  Proof.
   intros t s k m1 m2 H; destruct s; simpl.
   simpl in H.
   rewrite depend_only_fv_expr with (e:=D) (m2:=m2).
   rewrite depend_only_fv_expr with (e:=F) (m2:=m2).
   rewrite depend_only_fv_expr with (e:=X1) (m2:=m2).
   rewrite depend_only_fv_expr with (e:=X2) (m2:=m2).
   trivial.
   apply req_mem_weaken with (2:=H); auto with set.
   apply req_mem_weaken with (2:=H); auto with set.
   apply req_mem_weaken with (2:=H); auto with set.
   apply req_mem_weaken with (2:=H); auto with set.
   rewrite depend_only_fv_expr with (e:=D) (m2:=m2).
   rewrite depend_only_fv_expr with (e:=F) (m2:=m2).
   rewrite depend_only_fv_expr with (e:=N) (m2:=m2).
   trivial.
   apply req_mem_weaken with (2:=H); simpl; auto with set.
   apply req_mem_weaken with (2:=H); simpl; auto with set.
   apply req_mem_weaken with (2:=H); simpl; auto with set.
  Qed.

  Lemma lossless_support : forall k t (s:usupport t) (m:Mem.t k),
   mu (eval s m) (fun _ => 1)%U == 1%U.
  Proof.
   intros; destruct s; simpl;
     refine (exp_antimon_lossless _ _ _ _ _).
  Qed.

  Lemma discrete_support : forall k t (s:usupport t) (m:Mem.t k),
   is_Discrete (eval s m).
  Proof.
   intros; destruct s; simpl;
      apply exp_antimon_is_Discr.
  Qed.

  Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
   match s1, s2 with
   | choose_points D F X1 X2, choose_points D' F' X1' X2' => 
     E.eqb D D' && E.eqb F F' && E.eqb X1 X1' && E.eqb X2 X2' 
   |  choose_index D F N, choose_index D' F' N' =>  
      E.eqb D D' && E.eqb F F' && E.eqb N N' 
   | _, _ => false 
   end.

  Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
   if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
   else ~eq_dep T.type usupport t1 e1 t2 e2.
  Proof.
   intros t1 e1 t2 e2; destruct e1; destruct e2; simpl.
   generalize (E.eqb_spec D D0); destruct (E.eqb D D0);
   generalize (E.eqb_spec F F0); destruct (E.eqb F F0);
   generalize (E.eqb_spec X1 X0); destruct (E.eqb X1 X0);
   generalize (E.eqb_spec X2 X3); destruct (E.eqb X2 X3);
   simpl; intros; subst; trivial; intro W; inversion W; tauto.
   intro W; inversion W.
   intro W; inversion W.
   generalize (E.eqb_spec D D0); destruct (E.eqb D D0);
   generalize (E.eqb_spec F F0); destruct (E.eqb F F0);
   generalize (E.eqb_spec N N0); destruct (E.eqb N N0);
   simpl; intros; subst; trivial; intro W; inversion W; tauto.
  Qed.

  Lemma eqb_spec : forall t (e1 e2:usupport t),
   if eqb e1 e2 then e1 = e2 else e1 <> e2.
  Proof.
   intros t e1 e2.
   generalize (eqb_spec_dep e1 e2).
   case (eqb e1 e2); intro H.
   apply T.eq_dep_eq; trivial.
   intro Heq; apply H; rewrite Heq; constructor.
  Qed.

 End US.


 Module DE := MakeDExpr UT T Var Mem Uop O E US.

 Module I := MakeInstr UT T Var Proc Uop O Mem E US DE.

 Module SemI := SemInstr.Make UT T Var Proc Uop O Mem E US DE I.

 Export SemI.


 (* list of expressions *)
 Notation "{ x , .. , y }" := 
  (@dcons T.type E.expr _ _ x .. 
   (@dcons T.type E.expr _ _ y (@dnil T.type E.expr)) ..). 

 (* boolean expressions *)
 Notation "'!' x"   := (E.Eop O.Onot { x }) (at level 60).
 Notation "x && y"  := (E.Eop O.Oand {x,  y}).
 Notation "x || y"  := (E.Eop O.Oor {x, y}).
 Notation "x ==> y" := (E.Eop O.Oimp {x, y}).
 Notation "b '?' x '?:' y" := (E.Eop (O.Oif _) {b, x, y}) (at level 60).

 (* pair expressions *)
 Notation "'Efst' p" := (E.Eop (O.Ofst _ _) { p }) (at level 0).
 Notation "'Esnd' p" := (E.Eop (O.Osnd _ _) { p }) (at level 0).
 Notation "'(' x '|' y ')'" := (E.Eop (O.Opair _ _) {x,  y} ).

 (* list expressions *)
 Notation "'Nil' t" := (E.Ecte (E.Cnil t)) (at level 0).
 Notation "x '|::|' y" := 
  (E.Eop (O.Ocons _) {x, y}) (at level 60, right associativity).
 Notation "x |++| l" := 
  (E.Eop (O.Oappend _) {x,l}) (at level 60, right associativity).
 Notation Enth := (E.Eop (O.Onth _)).
 Notation "'Elen' p" := (E.Eop (O.Olength _) {p}) (at level 40).
 Notation "Y '[{' x '}]'" := (E.Eop (O.Onth _) {x, Y}) (at level 60).
 Notation "'Hd' Y" := (E.Eop (O.Ohd _) { Y }) (at level 160).

 (* equality *)
 Notation "x '=?=' y" := (E.Eop (O.Oeq_ _) {x, y}) (at level 70, no associativity).

 (* nat expressions *)
 Notation "x '+!' y"  := (E.Eop O.Oadd {x, y}) (at level 50, left associativity).
 Notation "x '<=!' y" := (E.Eop O.Ole {x, y}) (at level 50).
 Notation "x '<!' y"  := (E.Eop O.Olt {x, y}) (at level 50).

 (* support *)
 Notation "'pick_swap'" :=
   (fun D F X Y => DE.Duser (@choose_points T.type T.Nat T.User E.expr
     (fun T => T.Pair T T) (fun T => T.List T) D F X Y)) (at level 60).
 Notation "'pick_solution'" :=
   (fun D F N => DE.Duser (@choose_index T.type T.Nat T.User E.expr
     (fun T => T.Pair T T) (fun T => T.List T) D F N)) (at level 60).

 (* sets *)
 Notation "X '|-|' y" := 
  (E.Eop (O.Ouser Oremove) {X, y}) (at level 150, left associativity).
 Notation "X '|+|' y" := 
  (E.Eop (O.Ouser Oadd) {X, y}) (at level 150, left associativity).
 Notation "'compl' X" := (E.Eop (O.Ouser Ocompl) { X }) 
   (at level 160).

 (* natural expressions *)
 Notation "x '-!' y"  := (E.Eop O.Osub {x, y}) (at level 50, left associativity).

End Sem.


(** Semantics with optimizations *)
Module Entries (MS:FiniteQuasiMetricSpace). 

 Module SemO <: SEM_OPT.
 
  Module Sem := Sem MS.
  Export Sem.
  
  Definition simpl_op (op : Uop.t) : 
   E.args (Uop.targs op) -> E.expr (Uop.tres op) :=
   match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
    | op => fun args => E.Eop (O.Ouser op) args
   end.

  Implicit Arguments simpl_op [].

  Lemma simpl_op_spec : forall k op args (m:Mem.t k),
   E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
  Proof.
   intros; simpl; trivial.
  Qed.

 End SemO.

 Module BP := BaseProp.Make SemO.Sem.

End Entries.


Declare Module MS : FiniteQuasiMetricSpace.

Module Ent := Entries MS.

Module Tactics := BuildTac.Make Ent.
Export Tactics.

(* Some useful tactics *)
Ltac mem_upd_simpl :=
 repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff; 
  [ | discriminate])); trivial.
  
Ltac expr_simpl := 
 unfold EP1, EP2, notR, andR, orR, impR, E.eval_expr; simpl; 
  unfold O.eval_op; simpl; mem_upd_simpl.

Lemma Aux: (1 <= exp (2 * eps * Diameter))%R.
Proof.
 rewrite <-exp_0 at 1; apply exp_monotonic.
 repeat apply Rmult_le_pos; [ fourier | apply eps_pos | ].
 rewrite <-(Diam_spec (T.default 0 (T.User Point)) 
   (T.default 0 (T.User Point))); apply Delta_pos.
Qed.

Hint Resolve Aux.
