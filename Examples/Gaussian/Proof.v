Require Export Normal.
Require Export BuildTac.


Set Implicit Arguments.

Unset Strict Implicit.


(* *********************************************************************** *)
(*                                  SEMANTICS                              *)
(* *********************************************************************** *)
Parameter scale : forall (k:nat), R.
Variable scale_pos: forall k, (0 < scale k)%R.

Inductive uop : Type := . 

Inductive usupport_ (T_type:Type) 
 (T_Z:T_type) (E_expr:T_type ->Type) : T_type -> Type :=
 | Gaussian : forall (i:E_expr T_Z), @usupport_ _ T_Z E_expr T_Z.

Module Sem <: SEM.

(** * User-defined type module *)
Module UT <: UTYPE.

 Definition t := Empty_set. 
 
 Definition eqb (x y:t) := true.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  intros x; case x.
 Qed.

 Definition eq_dec (x y:t) : {x = y} + {True}.
  intros; case x; case y.
 Defined.

 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  intros x; case x.
 Qed.

 Definition interp (k:nat) (t0:t) : Type := Datatypes.unit.

 Definition size k (t0:t) (_:interp k t0) := S O.

 Definition default k (t0:t) : interp k t0 := tt.

 Definition default_poly (t0:t) := pcst 1.

 Lemma size_positive : forall k t0 (x:interp k t0), (0 < size x)%nat.
 Proof.
  intros; unfold size; auto with arith.
 Qed.

 Lemma default_poly_spec : forall k (t0:t),
  (size (default k t0) <= peval (default_poly t0) k)%nat.
 Proof.
  intros; unfold size, default, default_poly.
  rewrite pcst_spec; trivial.
 Qed.

 Definition i_eqb k t (_:interp k t) (_:interp k t) := true.

 Lemma i_eqb_spec : forall k t (x y:interp k t), 
  if i_eqb x y then x = y else x <> y.
 Proof.
  intros; unfold i_eqb; case x; case y; trivial.
 Qed.

End UT.


Module T := MakeType UT.


(** * Module for user-defined operators *)
Module Uop <: UOP UT T.

 Definition t := uop.

 Definition eqb (o1 o2:t) : bool := true.

 Lemma eqb_spec :  forall x y, if eqb x y then x = y else x <> y.
 Proof.
  destruct x; destruct y; simpl.  
 Qed.

 Definition targs (op : t) : list T.type := nil.

 Definition tres (op: t) : T.type := T.Unit.


 Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) := 
  match op as op0 return T.type_op k (targs op0) (tres op0) with
   |
  end.

 Implicit Arguments interp_op [k].

 Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
  match op as op0 return T.ctype_op k (targs op0) (tres op0) with
   |
   end.

 Implicit Arguments cinterp_op [k].
 
 Definition eval_op k
  (op:t) (args:dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
  @T.app_op k (targs op) (tres op) (interp_op op) args.

 Definition ceval_op k 
  (op:t) (args:dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
  @T.capp_op k (targs op) (tres op) (cinterp_op op) args.

 Lemma ceval_op_spec : forall k op args,
  @eval_op k op args = fst (@ceval_op k op args).
 Proof.
  intros k o args; destruct o; simpl in args;
   T.dlist_inversion args; subst; simpl; trivial.
 Qed.

End Uop.


Module Var := MakeVar UT T.

Module Proc := MakeProc UT T.

Module O := MakeOp UT T Uop.

Module Mem := MakeMem UT T Var.

Module E := MakeExpr UT T Var Mem Uop O.

Module US <: USUPPORT UT T Var Mem Uop O E.

 Module VarP := MkEqBool_Leibniz_Theory Var.
 Module Vset := MkListSet VarP.Edec.

 Definition usupport := usupport_ T.Zt E.expr .

 Definition eval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) :=
  match s with
   | Gaussian a => Normal (scale k) (E.eval_expr a m)
  end.

 Definition ceval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) * nat :=
  match s with
   |  Gaussian a => (Normal (scale k) (E.eval_expr a m), T.size k T.Zt (E.eval_expr a m))
  end.

 Lemma ceval_spec : forall k t (s:usupport t) (m:Mem.t k), 
  eval s m = fst (ceval s m).
 Proof.
  intros; case s; intros; simpl; trivial.
 Qed.   


 (** TODO: add to EXPR *)
 Fixpoint fv_expr_rec (t:T.type) (res:Vset.t) (e:E.expr t) {struct e} : Vset.t :=
  match e with 
   | E.Ecte _ _ => res 
   | E.Evar t x => Vset.add x res 
   | E.Eop op args => dfold_left fv_expr_rec args res
   | E.Eexists t x e1 e2 => 
     Vset.union 
     (Vset.remove x (fv_expr_rec Vset.empty e1)) 
     (fv_expr_rec res e2)
   | E.Eforall t x e1 e2 => 
     Vset.union 
     (Vset.remove x (fv_expr_rec Vset.empty e1))
     (fv_expr_rec res e2)
   | E.Efind t x e1 e2 => 
     Vset.union 
     (Vset.remove x (fv_expr_rec Vset.empty e1))
     (fv_expr_rec res e2)
  end.

 Definition fv_expr t := @fv_expr_rec t Vset.empty.

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
 
 Axiom depend_only_fv_expr : forall t (e:E.expr t), depend_only (fv_expr e) e.

 Definition fv_distr t (s:usupport t) : Vset.t :=
  match s with
   | Gaussian a => (fv_expr a)
  end.

 Lemma depend_only_fv_distr : forall t (s:usupport t), 
  depend_only_distr (fv_distr s) s.
 Proof.
  intros t s k m1 m2 Hm.
  destruct t; destruct s; simpl in *;
   ((rewrite (depend_only_fv_expr Hm); trivial) || trivial).
 Qed.

 Lemma lossless_support : forall k t (s:usupport t) (m:Mem.t k),
  mu (eval s m) (fun _ => 1)%U == 1%U.
 Proof.
  intros; destruct s.
  apply (Normal_lossless _ _).
 Qed.

 Lemma discrete_support : forall k t (s:usupport t) (m:Mem.t k),
  is_Discrete (eval s m).
 Proof.
  intros; destruct s; simpl.
  apply Normal_Discrete.
 Qed.

 Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
  match s1, s2 with
  | Gaussian a, Gaussian a' => E.eqb a a' 
  end.

 Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
  if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
  else ~eq_dep T.type usupport t1 e1 t2 e2.
 Proof.
  intros t1 u1 t2 u2; destruct u1; destruct u2; simpl.
  generalize (E.eqb_spec i i0); destruct (E.eqb i i0); intros; simpl; 
   intros; subst; trivial; intro W; inversion W; tauto.
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


 Notation "{ x , .. , y }" := 
  (@dcons T.type E.expr _ _ x .. 
   (@dcons T.type E.expr _ _ y (@dnil T.type E.expr)) ..). 

 (* Boolean expressions *)
 Notation "'!' x"   := (E.Eop O.Onot { x }) (at level 60).
 Notation "x && y"  := (E.Eop O.Oand {x,  y}).
 Notation "x || y"  := (E.Eop O.Oor {x, y}).
 Notation "x ==> y" := (E.Eop O.Oimp {x, y}).
 Notation "b '?' x '?:' y" := (E.Eop (O.Oif _) {b, x, y}) (at level 60).

 (* pair expressions *)
 Notation "'Efst' p" := (E.Eop (O.Ofst _ _) { p }) (at level 0).
 Notation "'Esnd' p" := (E.Eop (O.Osnd _ _) { p }) (at level 0).
 Notation "'(' x '|' y ')'" := (E.Eop (O.Opair _ _) {x,  y} ).

 (* sum expressions *)
 Notation "'Inl' x" := (E.Eop (O.Oinl _ _) { x }) (at level 60).
 Notation "'Inr' x" := (E.Eop (O.Oinr _ _) { x }) (at level 60).
 Notation "'Isl' x" := (E.Eop (O.Oisl _ _) { x }) (at level 60).
 Notation "'Projl' x" := (E.Eop (O.Oprojl _ _) { x }) (at level 60).
 Notation "'Projr' x" := (E.Eop (O.Oprojr _ _) { x }) (at level 60).

 (* option expressions *)
 Notation "'none' t" := (E.Ecte (E.Cnone t)) (at level 0).
 Notation "'some' x" := (E.Eop (O.Osome _) { x }) (at level 60).
 Notation "'IsSome' x" := (E.Eop (O.Oissome _) { x }) (at level 60).
 Notation "'Proj' x" := (E.Eop (O.Oprojo _) { x }) (at level 60).

 (* list expressions *)
 Notation "'Nil' t" := (E.Ecte (E.Cnil t)) (at level 0).
 Notation "x '|::|' y" := 
  (E.Eop (O.Ocons _) {x, y}) (at level 60, right associativity).
 Notation "'Etail' p" := (E.Eop (O.Otl _) {p}) (at level 40).
 Notation "'Ehead' p" := (E.Eop (O.Ohd _) {p}) (at level 40).
 Notation "'Elen' p" := (E.Eop (O.Olength _) {p}) (at level 40).
 Notation "x |++| l" := 
  (E.Eop (O.Oappend _) {x,l}) (at level 60, right associativity).

 (* association lists *)
 Notation "x 'in_dom' y" := (E.Eop (O.Oin_dom _ _) {x, y}) (at level 60).
 Notation "x 'in_range' y" := (E.Eop (O.Oin_range _ _) {x, y}) (at level 60).
 Notation "y '[{' x '}]'" := (E.Eop (O.Oimg _ _) {x, y}) (at level 59).
 Notation "l '.[{' x '<<-' v '}]'" := 
   (E.Eop (O.Oupd _ _) {x,v,l}) (at level 50).

 (* nat expressions *)
 Notation "x '+!' y"  := (E.Eop O.Oadd {x, y}) (at level 50, left associativity).
 Notation "x '*!' y"  := (E.Eop O.Omul {x, y}) (at level 40, left associativity).
 Notation "x '-!' y"  := (E.Eop O.Osub {x, y}) (at level 50, left associativity).
 Notation "x '<=!' y" := (E.Eop O.Ole {x, y}) (at level 50).
 Notation "x '<!' y"  := (E.Eop O.Olt {x, y}) (at level 50).

 (* Z expressions *)
 Notation "x '+Z' y"   := (E.Eop O.OZadd {x, y}) (at level 50, left associativity).
 Notation "x '*Z' y"   := (E.Eop O.OZmul {x, y}) (at level 40, left associativity).
 Notation "x '-Z' y"   := (E.Eop O.OZsub {x, y}) (at level 50, left associativity).
 Notation "x '<=Z' y"  := (E.Eop O.OZle {x, y}) (at level 50).
 Notation "x '<Z' y"   := (E.Eop O.OZlt {x, y}) (at level 50).
 Notation "x '>=Z' y"  := (E.Eop O.OZge {x, y}) (at level 50).
 Notation "x '>Z' y"   := (E.Eop O.OZgt {x, y}) (at level 50).
 Notation "'oppZ' x"   := (E.Eop O.OZopp {x}) (at level 40).
 Notation "x '/Z' y"   := (E.Eop O.OZdiv {x, y}) (at level 50).
 Notation "x 'modZ' y" := (E.Eop O.OZmod {x, y}) (at level 50).
 Notation "x 'powZ' y" := (E.Eop O.OZpow {x, y}) (at level 50).

 (* equality *)
 Notation "x '=?=' y" := (E.Eop (O.Oeq_ _) {x, y}) (at level 70, no associativity).

 (* distribution expressions *)
 Notation "'{0,1}'" := DE.Dbool.
 Notation "'[0..' e ']'" := (DE.Dnat e)%nat.
 Notation "'[' e1 ',,' e2 ']'" := (DE.DZ e1 e2)%nat.
 Notation "'Norm' a" := (DE.Duser (@Gaussian  _ _ E.expr a)) (at level 60).

End Sem.


(** Semantics with optimizations *)
Module Entries. 

 Module SemO <: SEM_OPT.
 
  Module Sem := Sem.
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


Module Ent := Entries.

Module Tactics := BuildTac.Make Ent.
Export Tactics.




(* *********************************************************************** *)
(*                             GAUSSIAN MECHANISM                          *)
(* *********************************************************************** *)
Section GAUSSIAN_MECHANISM.

 Variable delta: nat -o> U.
 Variable epsilon: nat -> R.
 Hypothesis eps_pos: forall k, (0 <= epsilon k)%R.


 Variable E1 E2 : env.
 Variable a1 : Var.var T.Zt.
 Variable a2 : Var.var T.Zt.
 Variable r : Var.var T.Zt.

 Let Z_Gt := fun (L:R) (z:Z) => if Rlt_dec L (IZR z) then 1%U else D0.

 Let Pre  k (m1 m2:Mem.t k) := 
   let t := IZR (m1 a1 - m2 a2)%Z in
   let alpha := ((scale k * epsilon k - Rsqr t) / (2 * Rabs t))%R in
      (mu (Normal (scale k) 0%Z) (Z_Gt alpha) <= delta k)%tord.

 Lemma Gaussian_Mech: 
  eequiv Pre 
  E1 [ r <$- Norm  a1 ]
  E2 [ r <$- Norm  a2 ]
  (kreq_mem {{r}}) (fun k => exp (epsilon k)) delta.
 Proof.
  intros.
  apply eequiv_weaken with Pre (EP_eq_expr r r) 
    (fun k => exp (epsilon k))  delta; trivial.
  unfold EP_eq_expr; intros k m1 m2 Hm t v Hv; 
   Vset_mem_inversion Hv; subst; auto.
  refine (@eequiv_random_discr _ _ _ _ _ _ _ _ _ delta _ _);
    [ auto | ].
  intro k; rewrite <-exp_0; apply exp_monotonic; trivial.
  unfold Pre; intros k m1 m2 H.
  eapply Normal_dist; [ | intro z; apply (cover_dec  (Z_eq_dec z)) | | ].
    apply scale_pos.
    rewrite <-exp_0; apply exp_monotonic; trivial.
    rewrite ln_exp; exact H.
 Qed.

End GAUSSIAN_MECHANISM.

