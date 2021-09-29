Require Export BuildTac.

Set Implicit Arguments.

Unset Strict Implicit.

Lemma iU_eq_inv: forall x y : R,
 (0 <= x <= 1)%R -> 
 (0 <= y <= 1)%R -> 
 iU x == iU y -> 
 x = y.
Proof.
 intros x y Hx Hy (H1,H2).
 apply Rle_antisym; apply iU_le_inv; trivial.
Qed.

Lemma iU_div_distr: forall x y, 
 (0 <= x <= y)%R ->
 (0 < y <= 1)%R ->
 iU x / iU y <= iU (x / y).
Proof.
 intros x y [H1 H2] [H3 H4].
 assert (~0 == iU y).
 rewrite <-iU_0; intro Heq; apply iU_eq_inv in Heq.
 fourier.
 split; fourier.
 split; fourier.
 
 apply Umult_le_simpl_left with (1:=H).
 rewrite Umult_div; auto.
 rewrite <-iU_mult, Rmult_comm, Rdiv_mult; trivial.
 split; fourier.
 split; [apply Rdiv_pos | apply Rdiv_le_1]; fourier.
Qed.


Opaque sigma.

Lemma lub_Udiv: forall f x,
 (lub (c:=U) (sigma f)) / x  == lub (c:=U) (sigma (fdiv x f)).
Proof.
 intros.
 eapply Oeq_trans; 
  [ apply (@lub_comp_eq _ _ (UDiv x) (sigma f) (Udiv_continuous _)) | ].
 apply lub_eq_compat; refine (ford_eq_intro _); intro n.
 simpl; induction n.
 rewrite sigma_0; auto.
 rewrite 2 sigma_S, Udiv_plus; 
 apply Uplus_eq_compat; trivial.
Qed.

Transparent sigma.


Parameter Lsize : forall (k:nat), nat.

Parameter NChunks : forall (k:nat), nat.

Parameter Eps : forall (k:nat), R.

Variable eps_pos : forall k, (0 < Eps k)%R.

Hypothesis Lsize_pos : forall k, (0 < Lsize k)%nat.

Inductive uop : Type :=
 | N
 | Q
 | ODrop
 | OTake 
 | OMapPlus.

Inductive usupport_ (T_type:Type) 
 (T_Z:T_type) (T_List_Z:T_type) (E_expr:T_type ->Type) : T_type -> Type :=
 | Lap    : forall (i:E_expr T_Z), @usupport_ _ T_Z T_List_Z E_expr T_Z
 | MapLap : forall (l:E_expr T_List_Z), @usupport_ _ T_Z T_List_Z E_expr T_List_Z.

Fixpoint ListLaplace (eps:R) (l:list Z) {struct l} : Distr (list Z) :=
 match l with
  | nil => Munit nil
  | x::xs => Mlet (ListLaplace eps xs) 
              (fun zs => Mlet (Laplace eps x) (fun z => Munit (z::zs)))
 end.

Lemma Laplace_lossless : forall (eps:R) (a:Z),
 mu (Laplace eps a) (fone _) == 1.
Proof.
  apply Laplace_lossless.
Qed.

Lemma ListLaplace_lossless : forall (eps:R),
 forall (l:list Z),
 mu (ListLaplace eps l) (fone _) == 1.
Proof.
 intros eps.
 induction l.
 trivial.
 rewrite <-IHl.
 simpl ListLaplace; rewrite Mlet_simpl.
 refine (mu_stable_eq _ _ _ _); refine (ford_eq_intro _); intro l'.
 rewrite Mlet_simpl.
 apply Laplace_lossless.
Qed.

Lemma Laplace_Discrete: forall (eps:R) (a:Z),
 is_Discrete (Laplace eps a).
Proof.
 apply Laplace_is_Discrete.
Qed.

Lemma ListLaplace_Discrete: forall (eps:R) (l: list Z),
 is_Discrete (ListLaplace eps l).
Proof.
 induction l; simpl.
 apply is_Discrete_Munit.
 apply (is_Discrete_Mlet _ IHl).
 intro; apply (is_Discrete_Mlet _ (Laplace_Discrete _ _)).
 intro; apply is_Discrete_Munit.
Qed.


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

 Definition eqb (o1 o2:t) : bool := 
  match o1, o2 with
   | N, N => true
   | Q, Q => true
   | ODrop, ODrop => true
   | OTake, OTake => true
   | OMapPlus, OMapPlus => true
   | _, _ => false
   end.

 Lemma eqb_spec :  forall x y, if eqb x y then x = y else x <> y.
 Proof.
  destruct x; destruct y; simpl; (trivial || discriminate).
 Qed.

 Definition targs (op : t) : list T.type := 
  match op with
   | N => nil
   | Q => nil
   | ODrop => (T.List T.Zt) :: nil
   | OTake => (T.List T.Zt) :: nil
   | OMapPlus => T.Zt :: (T.List T.Zt) :: nil 
  end.

 Definition tres (op: t) : T.type := 
  match op with
   | N => T.Nat 
   | Q => T.Nat
   | ODrop => T.List T.Zt
   | OTake => T.List T.Zt
   | OMapPlus => T.List T.Zt
  end.

 Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) := 
  match op as op0 return T.type_op k (targs op0) (tres op0) with
   | N => Lsize k
   | Q => NChunks k
   | ODrop => @skipn Z (Lsize k)
   | OTake => @firstn Z (Lsize k)
   | OMapPlus => (fun n l => map (Zplus n) l)
 end.

 Implicit Arguments interp_op [k].

 Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
  match op as op0 return T.ctype_op k (targs op0) (tres op0) with
   | N => (Lsize k, S O)
   | Q => (NChunks k, S O)
   | ODrop => fun l => (@skipn Z (Lsize k) l,
                        T.size k (T.List T.Zt) (firstn (Lsize k) l))
   | OTake => fun l => (@firstn Z (Lsize k) l,
                        T.size k (T.List T.Zt) (firstn (Lsize k) l))
   | OMapPlus => fun n l => (map (Zplus n) l, T.size k (T.List T.Zt) l)
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

 Definition usupport := usupport_ T.Zt (T.List T.Zt) E.expr .

 Definition eval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) :=
  match s with
   | Lap a => Laplace (Eps k) (E.eval_expr a m)
   | MapLap l => ListLaplace (Eps k) (E.eval_expr l m)
  end.

 Definition ceval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) * nat :=
  match s with
   | Lap a => (Laplace (Eps k) (E.eval_expr a m), T.size k T.Zt (E.eval_expr a m))
   | MapLap l => (ListLaplace (Eps k) (E.eval_expr l m), 
                  T.size k (T.List T.Zt) (E.eval_expr l m))
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
   | Lap a => (fv_expr a)
   | MapLap l => (fv_expr l)
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
  apply Laplace_lossless.
  apply ListLaplace_lossless.
 Qed.

 Lemma discrete_support : forall k t (s:usupport t) (m:Mem.t k),
  is_Discrete (eval s m).
 Proof.
  intros; destruct s; simpl.
  apply Laplace_Discrete.
  apply ListLaplace_Discrete.
 Qed.

 Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
  match s1, s2 with
  | Lap a, Lap a' => E.eqb a a' 
  | MapLap l, MapLap l' => E.eqb l l' 
  | _, _ => false
  end.

 Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
  if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
  else ~eq_dep T.type usupport t1 e1 t2 e2.
 Proof.
  intros t1 u1 t2 u2; destruct u1; destruct u2; simpl.
  generalize (E.eqb_spec i i0); destruct (E.eqb i i0); intros; simpl; 
   intros; subst; trivial; intro W; inversion W; tauto.
  intro W; inversion W; tauto.
  intro W; inversion W; tauto.
  generalize (E.eqb_spec l l0); destruct (E.eqb l l0); intros;
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
 Notation "'Lap' a" := (DE.Duser (@Lap _ _ _ E.expr a)) (at level 60).
 Notation "'MapLap' 'eps'" := 
  (fun l => DE.Duser (@MapLap T.type T.Zt (T.List T.Zt) E.expr l)) (at level 60).

 (* User-defined operators *)
 Notation "'q'" := (E.Eop (O.Ouser Q) (dnil E.expr)) (at level 60).
 Notation "'N'" := (E.Eop (O.Ouser N) (dnil E.expr)) (at level 60).
 Notation "'Efirstn'  x" := (E.Eop (O.Ouser OTake) {x}) (at level 60).
 Notation "'Elastn'  x" := (E.Eop (O.Ouser ODrop) {x}) (at level 60).
 Notation "'MapPlus'  x l" := (E.Eop (O.Ouser OMapPlus) {x,l}) (at level 60).

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


(* Boolean comparability in U *)
Parameter Uleb : U -> U -> bool.

Hypothesis Uleb_spec: forall (u1 u2:U), if Uleb u1 u2 then u1 <= u2 else u2 < u1.

Lemma Uleb_corr_conv: forall (x y: U), 
 (x <= y)%tord -> Uleb x y.
Proof.
 intros u1 u2 H.
 generalize (Uleb_spec u1 u2).
 case_eq (Uleb u1 u2); intros Heq H'.
 trivial.
 contradiction.
Qed.

Lemma Uleb_compl_conv: forall (u1 u2: U), 
 (u2 < u1)%U -> Uleb u1 u2 = false.
Proof.
 intros u1 u2 H.
 generalize (Uleb_spec u1 u2).
 case_eq (Uleb u1 u2); intros Heq H'.
 contradiction.
 trivial.
Qed.


(* Multiplication of a real by a natural number *)
Fixpoint RNmult (r:R) (n:nat) {struct n} :=
 match n with 
  | 0%nat => 0%R
  | S n'' => (r + (RNmult r n''))%R
 end.
    
Lemma RNmult_ge_0: forall (r:R) (n:nat),
 (0 <= r)%R ->
 (0 <= RNmult r n)%R.
Proof.
 induction n; intros; simpl.
 auto.
 rewrite <-(Rplus_0_r 0); apply Rplus_le_compat; auto.
Qed.

Lemma exp_Rmult: forall (r:R) (n:nat),
 (exp r ^ n = exp (RNmult r n))%R.
Proof.
 induction n; simpl; symmetry.
 apply exp_0.
 rewrite IHn; apply exp_plus.
Qed.


(* Some useful tactics *)
Ltac mem_upd_simpl :=
 repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff; 
  [ | discriminate])); trivial.
  
Ltac expr_simpl := 
 unfold EP1, EP2, notR, andR, orR, impR, E.eval_expr; simpl; 
  unfold O.eval_op; simpl; mem_upd_simpl.


(* Some auxiliary lemmas *)
Lemma Zeq_bool_comm: forall z1 z2, Zeq_bool z1 z2 = Zeq_bool z2 z1.
Proof.
 intros.
 case_eq (Zeq_bool z1 z2); intro Heq.
 symmetry; rewrite <-(@Zeq_is_eq_bool z2 z1); symmetry.
 apply (Zeq_bool_eq _ _ Heq).
 symmetry; apply not_true_iff_false; intro H'.
 apply ((Zeq_bool_neq _ _ Heq) (eq_sym (Zeq_bool_eq _ _ H'))).
Qed.

Lemma Zeqb_list_bool_comm: forall l1 l2, 
 eqb_list Zeq_bool l1 l2 = eqb_list Zeq_bool l2 l1.
Proof.
 induction l1; intros; destruct l2; trivial.
 simpl; rewrite (Zeq_bool_comm a z), (IHl1 l2); trivial.
Qed.

Lemma multRU_le_Rmult : forall (u1 u2:U) (x:R),
 (0 <= x)%R ->
 (iR u1 <= x * iR u2)%R -> 
 u1 <= x ** u2.
Proof.
 intros u1 u2 x Hx H; unfold  multRU; repeat case_Rle.
 rewrite <-(retract_U u1); apply (iU_le H).
 elim n; apply Rmult_le_pos; auto.
 auto.
Qed.

Lemma nth_eq: forall (A:Type) (a:A) (l1 l2:list A),
 length l1 = length l2 ->
 (forall i, (i < length l1)%nat -> nth i l1 a  = nth i l2 a) ->
 l1 = l2.
Proof.
 induction l1; intros.
 destruct l2; [ trivial | discriminate ].
 destruct l2; [ discriminate | ].
 apply f_equal2.
 apply (H0 0%nat (lt_0_Sn _)).
 apply (IHl1 _ (eq_add_S _ _ H)).
 intros i Hi; apply (H0 (S i) (lt_n_S _ _ Hi)).
Qed.

Lemma int_between_0_1_inv: forall (z:Z), 
 (0 <= z <= 1%Z)%Z -> 
 z = 1%Z \/ z = 0%Z. 
Proof.  
 intros.
 destruct (Compare.le_le_S_eq _ _ (Zabs_nat_le _ _ H)).
 (* |z| = 0 *) 
 pose proof (le_n_0_eq _ (@le_S_n (Zabs_nat z) 0 H0)) as H'; clear H0.
 right; symmetry; unfold Zabs_nat in H'; case_eq z; intros; subst;
  try (pose proof (lt_O_nat_of_P p); exfalso; omega); trivial.
 (* |z| = 1 *)
 unfold Zabs_nat in H0; case_eq z; intros; rewrite H1 in H0.
 right; symmetry; trivial.
 left; rewrite (nat_of_P_inj _ _ H0); trivial.
 rewrite H1 in H; destruct H as [H' _];
  pose proof (Zlt_neg_0 p);   exfalso; omega.
Qed.

Lemma Zplus_diff_eq_compat_l: forall x y z,
 (x + y <> x + z)%Z ->
 (y <> z)%Z.
Proof.
 intros x y z H H'.
 elim H; rewrite H'; auto with arith.
Qed.

Lemma nat_eqb_eq: forall n1 n2,
 n1 = n2 ->
 nat_eqb n1 n2.
Proof.
 intros; subst; apply nat_eqb_refl.
Qed.

Lemma req_mem_upd_notin_r : forall k (m1 m2:Mem.t k) t (v2:Var.var t) e2 X, 
 req_mem X m1 m2 ->
 ~Vset.mem v2 X ->
 req_mem X m1 (m2 {!v2 <-- e2!}).
Proof.
 intros; intros t0 x Hx.
 repeat rewrite Mem.get_upd_diff.
 apply H; trivial.
 intro Heq; elim H0; rewrite Heq; trivial.
Qed.

Lemma length_skipn_le: forall (A:Type) (l:list A) n,
 (length (skipn n l) <= length l)%nat.
Proof.
 induction l; intros; destruct n; simpl; auto.
Qed.

Lemma req_mem_upd_notin : forall k (m1 m2:Mem.t k) t1 t2 
 (v1: Var.var t1) (v2: Var.var t2) e1 e2 X, 
 req_mem X m1 m2 ->
 ~Vset.mem v1 X ->
 ~Vset.mem v2 X ->
 req_mem X (m1 {!v1 <-- e1!}) (m2 {!v2 <-- e2!}).
Proof.
 intros; intros t0 x Hx.
 repeat rewrite Mem.get_upd_diff.
 apply H; trivial.
 intro Heq; elim H1; rewrite Heq; trivial.
 intro Heq; elim H0; rewrite Heq; trivial.
Qed.

Lemma lam_ge_1: forall k, (1 <= exp (Eps k))%R.
Proof.
 intro k; rewrite <-exp_0; apply (exp_monotonic (Rlt_le _ _ (eps_pos k))).
Qed.

Lemma exp_eps_ge_1: forall k n, 
 (1 <= exp (Eps k * INR n))%R.
Proof.
 intros k n; rewrite <-exp_0; apply exp_monotonic;
  apply (Rmult_le_pos _ _  (Rlt_le _ _ (eps_pos k)) (pos_INR _)).
Qed.

Hint Resolve exp_eps_ge_1 lam_ge_1 RNmult_ge_0.

Lemma length_firstn_compat: forall (A:Type) m (l1 l2:list A),
 length l1 = length l2 ->
 length (firstn m l1) = length (firstn m l2).
Proof.
 induction m.
 intros; trivial.
 intros.
 destruct l1; destruct l2; try discriminate; simpl.
 trivial.
 apply (eq_S _ _ (IHm _ _ (eq_add_S _ _ H))).
Qed.

Lemma length_skipn_compat: forall (A:Type) m (l1 l2:list A),
 length l1 = length l2 ->
 length (skipn m l1) = length (skipn m l2).
Proof.
 intros A m l1 l2 H; generalize H.
 rewrite <-(firstn_skipn m l1), <-(firstn_skipn m l2) at 1;
  rewrite 2 app_length, (length_firstn_compat _ H).
 intro H'; clear H.
 omega.
Qed.


Section NMATCH.

 Open Scope nat_scope.

 Variable A : Type.
 Variable P : A -> A -> bool.
 Variable def : A.

 Fixpoint NMatch (l1 l2:list A) {struct l1} : nat :=
  match l1,l2 with 
   | x::xs,y::ys => if P x y then S (NMatch xs ys) else (NMatch xs ys)
   | _,_ => 0%nat
  end.

 Variable P_spec :  forall (a1 a2:A), if P a1 a2 then a1 <> a2 else a1 = a2.

 Lemma P_non_refl : forall a, negb (P a a).
 Proof.
  intros.
  generalize (P_spec a a).
  case_eq (P a a); intro Heq.
  intro H; elim (H (eq_refl _)).
  simpl; trivial.
 Qed.

 Lemma NMatch_0 : forall l1 l2,
  length l1 = length l2 ->
  NMatch l1 l2 = 0%nat -> 
  l1 = l2.
 Proof.
  induction l1; intros.
  destruct l2; [ trivial | discriminate ].
  destruct l2; [ discriminate | ].
  simpl in  H0.
  generalize (P_spec a a0) H0; 
   case (P a a0); simpl; intros Haa0 Hip.
  discriminate.
  rewrite Haa0, (IHl1 _ (eq_add_S _ _ H) Hip); trivial.
 Qed.

 Lemma  NMatch_eq: forall l, NMatch l l = 0.
 Proof.
  induction l.
  trivial.
  simpl.
  rewrite <-(negb_involutive (P a a)), P_non_refl; simpl; trivial.
 Qed.

 Definition list_ApEq (l1 l2:list A) := NMatch l1 l2 <= 1.
 
 Lemma list_ApEq_tl_compat: forall l1 l2,
  length l1 = length l2 ->
  list_ApEq l1 l2 ->
  list_ApEq (tl l1) (tl l2).
 Proof.
  unfold list_ApEq; intros.
  destruct l1; destruct l2; try discriminate.
  apply le_trans with (2:=H0); trivial.
  apply le_trans with (2:=H0).
  simpl; destruct (P a a0); auto.  
 Qed.
 
 Lemma list_ApEq_first_compat: forall m l1 l2,
  length l1 = length l2 ->
  list_ApEq l1 l2 ->
  list_ApEq (firstn m l1) (firstn m l2).
 Proof.
  unfold list_ApEq.
  induction m; intros.
  simpl; auto with arith.
  destruct l1; destruct l2; try discriminate; simpl.
  auto with arith.
  simpl in H0; generalize (P_spec a a0); 
   destruct (P a a0); intro Heq.
  (* diff  *)
  apply le_n_S.
  cut (NMatch (firstn m l1) (firstn m l2) = 0%nat);
   [ intro H'; rewrite H'; auto | ].
  apply le_S_n in H0; apply le_n_0_eq in H0.
  rewrite (NMatch_0 (eq_add_S _ _ H) (eq_sym H0)).
  apply NMatch_eq.
  (* same *)
  apply (IHm _ _ (eq_add_S _ _ H) H0).
 Qed.

 Lemma NMatch_app: forall l1 l1' l2 l2',
  length l1 = length l1' ->
  NMatch (l1 ++ l2) (l1' ++ l2') = NMatch l1 l1' + NMatch l2 l2'.
 Proof.
  induction l1; intros.
  destruct l1'; [ trivial | discriminate ].
  destruct l1'; [ discriminate | ].
  repeat rewrite <-app_comm_cons.
  simpl; destruct (P a a0).
  apply (eq_S (NMatch (l1 ++ l2) (l1' ++ l2')) 
   ((NMatch l1 l1') + NMatch l2 l2')).
  apply (IHl1 _ _ _ (eq_add_S _ _ H)).
  apply (IHl1 _ _ _ (eq_add_S _ _ H)).
 Qed.
      
 Lemma list_ApEq_skipn_compat: forall m l1 l2,
  length l1 = length l2 ->
  list_ApEq l1 l2 ->
  list_ApEq (skipn m l1) (skipn m l2).
 Proof.
  unfold list_ApEq; intros m l1 l2.
  rewrite <-(firstn_skipn m l1) at 1 2.  
  rewrite <-(firstn_skipn m l2) at 1 2.
  intros.
  rewrite NMatch_app in H0.
  apply le_trans with (2:=H0); auto with arith.
  rewrite (firstn_skipn m l1), (firstn_skipn m l2) in H.
  apply (length_firstn_compat _ H).
 Qed.

 Lemma list_ApEq_eq: forall l1 l2,
  l1 = l2 ->
  list_ApEq l1 l2.
 Proof.
  unfold list_ApEq; intros; subst. 
  induction l2.
  auto.
  apply le_trans with (2:=IHl2).
  simpl.
  rewrite <-(negb_involutive (P a a)), (P_non_refl a); simpl; trivial.
 Qed.
  
 Lemma list_ApEq_hd_neq : forall l1 l2,
  length l1 = length l2 ->
  list_ApEq l1 l2 ->
  hd def l1 <> hd def l2 ->
  tl l1 = tl l2.
 Proof.
  unfold list_ApEq; intros; destruct l1; destruct l2;
   [ trivial | discriminate | discriminate | simpl in * ].
  generalize  (P_spec a a0) H0; clear H0; 
   case (P a a0); simpl; intros Haa0 Hip; [ | contradiction ].
  apply (NMatch_0 (eq_add_S _ _ H) (eq_sym (le_n_0_eq _ (le_S_n _ _ Hip)))).
 Qed.

 Lemma Nmatch_neq: forall l1 l2,
  length l1  = length l2 ->
  l1 <> l2 ->
  1 <= NMatch l1 l2.
 Proof.
  induction l1; intros.
  destruct l2; [ elim (H0 (eq_refl _)) | discriminate ].
  destruct l2; [ discriminate | ].
  simpl.
  generalize (P_spec a a0); destruct (P a a0); intros Heq.
  auto with arith.
  apply (IHl1 _ (eq_add_S _ _ H)).
  intro H'; elim H0; rewrite Heq, H'; trivial.
 Qed.
 
 Lemma list_ApEq_firstn_neq : forall m l1 l2,
  length l1 = length l2 ->
  list_ApEq l1 l2 ->
  firstn m l1 <> firstn m l2 ->
  skipn m l1 = skipn m l2.
 Proof.
  unfold list_ApEq; intros m l1 l2 Hlen.
  rewrite <-(firstn_skipn m l1), <-(firstn_skipn m l2) at 1.
  rewrite (NMatch_app _ _ (length_firstn_compat _ Hlen)).
  intros H1 H2.
  pose proof (Nmatch_neq (length_firstn_compat _ Hlen) H2); clear H2.
  apply (NMatch_0 (length_skipn_compat _ Hlen)).
  omega.
 Qed.

End NMATCH.


Lemma length_tl_compat: forall (A:Type) (l1 l2:list A),
 length l1 = length l2 ->
 length (tl l1) = length (tl l2).
Proof.
 intro A; destruct l1; destruct l2; simpl; intros.
 trivial.
 discriminate.
 discriminate.
 auto with arith.
Qed.

Lemma Zabs_le1_elim: forall x y,  (Zabs (x - y) <= 1)%Z ->
 (Zabs (x - y) = 1)%Z \/ x = y.
Proof.
 intros.
 destruct (int_between_0_1_inv (conj (Zabs_pos (x-y)) H)); clear -H0.
 left; trivial.
 right; destruct (Zabs_spec (x-y)) as [ (H2,H3) | (H2,H3) ]; 
  rewrite H3 in H0; omega.
Qed.

Definition DiffBound (l1 l2: list Z) (B:nat) := forall i, 
 (i < length l1)%nat ->
 (Zabs_nat (nth i l1 (0%Z) - nth i l2 (0%Z))%Z <= B)%nat.

Definition DiffBoundb  (l1 l2: list Z) (B:nat) :=
 forallb 
 (fun i => leb (Zabs_nat (nth i l1 (0%Z) - nth i l2 (0%Z))%Z) B)
 (seq 0 (length l1)).

Lemma DiffBoundb_iff: forall l1 l2 B,
 DiffBoundb l1 l2 B <-> DiffBound l1 l2 B. 
Proof.
 unfold DiffBoundb, DiffBound; intros l1 l2 B.
 rewrite is_true_forallb; split; intros H i Hi.
 refine (leb_complete _ _ (H i (le_In_seq _ _))); omega.
 apply In_seq_le in Hi.
 refine (leb_correct _ _ (H i _)); omega.
Qed.

Lemma DiffBound_tl_compat: forall n l1 l2,
 DiffBound l1 l2 n ->
 DiffBound (tl l1) (tl l2) n.
Proof.
 unfold DiffBound. 
 intros.
 destruct l1.
 elim (lt_n_O _ H0).    
 destruct l2.
 eapply le_trans; [ | apply (H (S i) (lt_n_S _ _ H0)) ];
  destruct i; simpl; auto.
 simpl.
 apply (H (S i) (lt_n_S _ _ H0)).
Qed.

Lemma DiffBound_app_r:forall n l1 l1' l2 l2',
 length l1 = length l2 ->
 DiffBound (l1 ++ l1') (l2 ++ l2') n ->
 DiffBound l1' l2' n.
Proof.
 induction l1; intros.
 destruct l2; [ apply H0 | discriminate ].
 destruct l2; [ discriminate | ].
 apply (IHl1 _ l2 _ (eq_add_S _ _ H)). 
 repeat rewrite <-app_comm_cons in H0.
 apply (DiffBound_tl_compat H0).
Qed.

Lemma DiffBound_app_l:forall n l1 l1' l2 l2',
 length l1 = length l2 ->
 DiffBound (l1 ++ l1') (l2 ++ l2') n ->
 DiffBound l1 l2 n.
Proof.
 induction l1; intros.
 destruct l2; [ | discriminate ].
 intros i Hi; elim (lt_n_O _ Hi).
 destruct l2; [ discriminate | ].
 intros i Hi; destruct i.
 apply (H0 0%nat).
 rewrite <-app_comm_cons; apply (lt_le_trans _ _ _ Hi).
 simpl; rewrite app_length; apply le_n_S; auto with arith.
 simpl; refine (@IHl1 l1' _ l2' (eq_add_S _ _ H) _ _ (lt_S_n _ _ Hi)).
 rewrite <-app_comm_cons in H0.
 apply (DiffBound_tl_compat H0).
Qed.

Lemma DiffBound_firstn_compat: forall n m l1 l2,
 length l1 = length l2 ->
 DiffBound l1 l2 n ->
 DiffBound (firstn m l1) (firstn m l2) n.
Proof.
 intros n m l1 l2 Hlen.
 rewrite <-(firstn_skipn m l1), <-(firstn_skipn m l2) at 1.
 intro H.
 refine (DiffBound_app_l (length_firstn_compat _ Hlen) H).
Qed.

Lemma DiffBound_skipn_compat: forall n m l1 l2,
 length l1 = length l2 ->
 DiffBound l1 l2 n ->
 DiffBound (skipn m l1) (skipn m l2) n.
Proof.
 intros n m l1 l2 Hlen.
 rewrite <-(firstn_skipn m l1), <-(firstn_skipn m l2) at 1.
 intro H.
 refine (DiffBound_app_r (length_firstn_compat _ Hlen) H).
Qed.

Lemma DiffBound_eq: forall M l1 l2,
 l1 = l2 -> 
 DiffBound l1 l2 M.   
Proof.
 intros; subst; unfold DiffBound; induction l2.
 intros i _; destruct i; simpl; apply le_0_n.
 intros i Hi; destruct i.
 simpl; rewrite Zminus_diag; apply le_0_n.
 apply (IHl2 i (lt_S_n _ _ Hi)).
Qed.

Hint Resolve length_tl_compat length_skipn_compat DiffBound_tl_compat 
 DiffBound_skipn_compat 
 (@list_ApEq_tl_compat Z (fun a b : Z => negb (Zeq_bool a b))) 
 (@list_ApEq_skipn_compat Z (fun a b : Z => negb (Zeq_bool a b))) 
 list_ApEq_eq 
 (@list_ApEq_first_compat Z (fun a b : Z => negb (Zeq_bool a b))) 
 length_firstn_compat : list_op DiffBound_firstn_compat.

Definition Zlist_ApEq := list_ApEq (fun a b:Z => negb (Zeq_bool a b)).

Lemma nZeq_bool_spec: forall (a1 a2:Z), 
 if negb (Zeq_bool a1 a2) then a1 <> a2 else a1 = a2.
Proof.
 intros; unfold negb; generalize (Zeq_bool_if a1 a2).
 case (Zeq_bool a1 a2); trivial.
Qed.

Definition  Zlist_ApEqb (l1 l2: list Z) := 
 leb (NMatch (fun a b:Z => negb (Zeq_bool a b)) l1 l2) 1%nat.

Lemma  Zlist_ApEqb_iff: forall (l1 l2: list Z),
 Zlist_ApEqb l1 l2 <->  Zlist_ApEq l1 l2.
Proof.
 unfold Zlist_ApEq, list_ApEq, Zlist_ApEqb; intros.
 apply leb_iff.
Qed.


Section LOOP_RULE.

 Variable c : cmd.
 Variable E : env.

 Variable A : T.type.
 Variable L : Var.var (T.List A).
 
 Variable I : mem_rel.

 Variable lam : nat -> R. 
 Variable ep : nat -o> U.
 Variable Size : nat -> nat.

 Hypothesis Size_pos : forall k, (0 < Size k)%nat.

 Variable A_eqb_dec : forall k (x y: T.interp k A), sumbool (x = y) (x <> y).

 Hypothesis HI : forall k (m1 m2:Mem.t k),
  I m1 m2 -> 
  length (m1 L) = length (m2 L).

 Hypothesis Hc : forall k (m:Mem.t k),
  range (fun m':Mem.t k => m' L = skipn (Size k) (m L)) ([[c]] E m).
 
 Hypothesis Hlam : forall k, (1 <= lam k)%R.
 
 Hypothesis H_eq_Hd :
  eequiv 
  (I /-\ 
   (fun k (m1 m2:Mem.t k) => firstn (Size k) (m1 L) = firstn (Size k) (m2 L) /\
   (m1 L) <> (m2 L)))
  E c E c 
  I 
  (fun _ => R1) (fzero _).
 
 Hypothesis H_diff_Hd :
  eequiv 
  (I /-\ (fun k (m1 m2:Mem.t k) => 
   firstn (Size k) (m1 L) <> firstn (Size k) (m2 L))) 
  E c E c 
  (I /-\ kreq_mem {{L}})
  lam ep.

 Hypothesis Hnoninter:
  eequiv 
   (I /-\ kreq_mem {{L}}) 
   E c E c 
   (I /-\ kreq_mem {{L}}) 
   (fun _ => R1) (fzero _).

 Opaque leb.

 Lemma loop_sem : forall k (m:Mem.t k),  
  [[ [while (0%nat <! Elen L) do c] ]] E m == 
  drestr ([[ unroll_while (0%nat <! Elen L) c (length (m L)) ]] E m) 
  (negP (@EP k (0%nat <! Elen L))).
 Proof.
  intros.
  apply eq_distr_intro; intro f.
  apply deno_bounded_while_elim with (Elen L).
  intros k' m' Hm'. 
  apply range_weaken with (2:=@Hc _ m').
  intros m''; generalize Hm'; clear Hm'.
  unfold EP; expr_simpl; unfold is_true; rewrite 2 leb_iff.
  destruct (m' L); simpl; intros.
  exfalso; omega.
  rewrite H0.
  generalize (Size_pos k'); destruct (Size k').
  intro H'; elim (lt_irrefl _ H').
  simpl; intros _; rewrite plus_comm; apply (le_n_S _ _ (length_skipn_le i0 n)).
  intros m'; expr_simpl; intro Hm'; rewrite Hm'.
  apply leb_correct_conv; auto with arith.
  apply le_refl.
 Qed.

 Definition DistrSel k 
  (d1 d2 d3:Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k)) (mm:Mem.t k * Mem.t k)
  : Distr (Mem.t k * Mem.t k).
  intros.
  destruct (E.eval_expr (0%nat <! Elen L) (fst mm)).
  destruct (list_eq_dec (@A_eqb_dec k) (firstn (Size k) (fst mm L))
   (firstn (Size k) (snd mm L))).
  destruct (req_mem_dec {{L}} (fst mm) (snd mm)).
  exact (d2 (fst mm) (snd mm)).
  exact (d1 (fst mm) (snd mm)).
  exact (d3 (fst mm) (snd mm)).
  exact (Munit mm).
 Defined.

 Fixpoint WitIter k (d1 d2 d3:Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k))
  (mm:Mem.t k * Mem.t k) (n:nat) : Distr (Mem.t k * Mem.t k) :=
  match n with 
   | S n' =>  Mlet (DistrSel d1 d2 d3 mm) (fun mm' => WitIter d1 d2 d3 mm' n')
   | 0%nat => 
    drestr (Munit mm) (fun mm => (negP (EP k (0%nat <! Elen L))) (fst mm))
  end.

 Definition WitD k n (m1 m2:Mem.t k) := 
  WitIter  
  (fun m1' m2' => proj1_sig (H_eq_Hd  m1' m2'))
  (fun m1' m2' => proj1_sig (Hnoninter m1' m2'))
  (fun m1' m2' => proj1_sig (H_diff_Hd m1' m2')) 
  (m1, m2) n.
 
 Ltac destr_sig :=  
  let d := fresh "d" in
  let Hd := fresh "Hd" in
   match goal with
    |- context [(proj1_sig ?x)]  => destruct x as (d,Hd); simpl proj1_sig
   end.
 
 Lemma HI_syn: forall k (m1 m2:Mem.t k), 
  I m1 m2 -> 
  E.eval_expr (0%nat <! Elen L) m2 = E.eval_expr (0%nat <! Elen L) m1. 
 Proof.
  intros; expr_simpl; setoid_rewrite (HI H); trivial.
 Qed.

 Lemma WitD_guard_false : forall k n (m1 m2:Mem.t k),
  I m1 m2 ->
  E.eval_expr (0%nat <! Elen L) m1 = false ->
  le_lift ((I /-\ EP1 (Elen L =?= 0%nat)) k)
  (WitD n m1 m2)
  (drestr (Munit m1) (negP (EP k (0%nat <! Elen L))))
  (drestr (Munit m2) (negP (EP k (0%nat <! Elen L))))
  1 0.
 Proof.
  unfold WitD. 
  induction n; intros m1 m2 H1m H2m; unfold WitD; simpl. 
 
  (* base case *)
  unfold drestr; rewrite 3 Mlet_unit.
  unfold negP, EP, negb; setoid_rewrite (@HI_syn _ _ _ H1m).
  case_eq (@E.eval_expr _ T.Bool (0%nat <! Elen L) m1); 
   intro Heq; setoid_rewrite Heq.
  eapply le_lift_eq_compat; [ apply Oeq_refl | | | | |
   apply le_lift_prod ]; auto.
  apply le_lift_Munit; auto.
  split; trivial; generalize Heq; clear Heq; expr_simpl;
   intro Heq; apply leb_complete_conv in Heq; apply nat_eqb_eq; omega.
 
  (* inductive case *)
  rewrite le_lift_lift.
  eapply lift_Mlet with ((I /-\ EP1 (Elen L =?= 0%nat)) k).
  unfold DistrSel; simpl fst; simpl snd.
  case_eq (@E.eval_expr _ T.Bool (0%nat <! Elen L) m1); intro Heq; 
   setoid_rewrite Heq.
  elim (eq_true_false_abs _ Heq H2m). 
  apply lift_unit.
  split; trivial; generalize Heq; clear Heq; expr_simpl;
   intro Heq; apply leb_complete_conv in Heq; apply nat_eqb_eq; omega.
  intros m1' m2' (H1m', H2m').
  rewrite <-le_lift_lift.
  eapply le_lift_eq_compat; [ | | | | | apply (IHn _ _ H1m') ]; auto.
  generalize H2m'; clear H2m'; expr_simpl; intro H2m'; 
   apply nat_eqb_true in H2m'; rewrite H2m';
    apply leb_correct_conv; auto with arith.
 Qed.

 Lemma WitD_eq_L: forall k n (m1 m2:Mem.t k),
  I m1 m2 ->
  kreq_mem {{L}} m1 m2 ->
  le_lift ((I /-\ EP1 (Elen L =?= 0%nat)) k)
  (WitD n m1 m2)
  (drestr (([[unroll_while (0%nat <! Elen L) c n]]) E m1)
   (negP (EP k (0%nat <! Elen L))))
  (drestr (([[unroll_while (0%nat <! Elen L) c n]]) E m2)
   (negP (EP k (0%nat <! Elen L)))) 
  1 0.
 Proof.
  unfold WitD; induction n; intros m1 m2 H1m H2m.
  
  (* base case *)
  unfold drestr.
  rewrite (eq_distr_intro _ 
   (Munit m1) (unroll_while_0_elim E (0%nat <! Elen L) c m1)),
   (eq_distr_intro _ (Munit m2) (unroll_while_0_elim E (0%nat <! Elen L) c m2)).
  rewrite 2 Mlet_unit. 
  simpl; unfold drestr; rewrite Mlet_unit; simpl.
  unfold negP, negb, EP; setoid_rewrite (@HI_syn _ _ _ H1m).
  apply le_lift_weaken with ((I /-\ EP1 (Elen L =?= 0%nat)) k) R1 D0; auto.
  case_eq (E.eval_expr (0%nat <! Elen L) m1); intro Heq; setoid_rewrite Heq.
  eapply le_lift_eq_compat; [ apply Oeq_refl | | | | |
   apply le_lift_prod ]; auto.
  apply le_lift_Munit; auto.
  split; trivial; generalize Heq; clear Heq; expr_simpl;
   intro Heq; apply leb_complete_conv in Heq; apply nat_eqb_eq; omega.
  
  (* inductive case *)
  unfold drestr. 
  rewrite (Mlet_eq_compat (eq_distr_intro  _ _ (deno_cond_elim E (0%nat <! Elen L) 
   (c ++ unroll_while (0%nat <! Elen L) c n) nil m1)) (Oeq_refl _)),
  (Mlet_eq_compat (eq_distr_intro  _ _ (deno_cond_elim E (0%nat <! Elen L) 
   (c ++ unroll_while (0%nat <! Elen L) c n) nil m2)) (Oeq_refl _)).
  simpl WitIter; unfold DistrSel; simpl fst; simpl snd.
  setoid_rewrite (@HI_syn _ _ _ H1m).
  case_eq (@E.eval_expr _ T.Bool (0%nat <! Elen L) m1); intro Heq; 
   setoid_rewrite Heq.
  (* [guard = true] *)
  rewrite 2 deno_app, 2 Mcomp.
  destruct (list_eq_dec (@A_eqb_dec k) (firstn (Size k) (m1 L))
   (firstn (Size k) (m2 L))) as [Hhead | Hhead].
  (* same head *)
  destruct (req_mem_dec {{L}} m1 m2) as [ Heq' | Heq' ].
  (* same list *)
  destr_sig.
  apply le_lift_weaken with ((I /-\ EP1 (Elen L =?= 0%nat)) k)
   (R1 * R1)%R (max (D0 + R1 ** D0)%U (D0 + R1 ** D0)%U);
   [ trivial | auto with real  | repeat multRU_simpl; repeat Usimpl; auto | ].
  eapply le_lift_Mlet. 
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd (conj H1m H2m))).
  trivial.
  apply (Hd (conj H1m H2m)).
  intros m1' m2' (H1m',H2m'); apply (IHn _ _  H1m' H2m').
  (* diff list *)
  contradiction.  
  (* diff head *)
  elim Hhead; apply f_equal; apply (H2m _ L); auto with set.
  (* guard = false *)
  rewrite 2 deno_nil, 3 Mlet_unit.
  eapply le_lift_eq_compat; [ apply Oeq_refl | | | | |
   apply (@WitD_guard_false _ n _ _ H1m Heq) ]; auto.
 Qed.
          
 Lemma Parallel_loop:
  eequiv 
  I
  E [ while (0%nat <! Elen L) do c ]
  E [ while (0%nat <! Elen L) do c ]
  (I /-\  (EP1 (Elen L =?= 0%nat)))
  lam ep.
 Proof.
  intros k.
  cut (forall m1 m2, sig (fun d' => I m1 m2 ->
   le_lift ((I /-\ EP1 (Elen L =?= 0%nat)) k) d'
   (drestr ([[ unroll_while  (0%nat <! Elen L) c (length (m1 L)) ]] E m1) 
    (negP (EP k (0%nat <! Elen L)))) 
   (drestr ([[ unroll_while  (0%nat <! Elen L) c (length (m1 L)) ]] E m2) 
    (negP (EP k (0%nat <! Elen L) )))
   (lam  k) (ep k))).
  intros H m1 m2; destruct (H m1 m2) as (d,Hd).
  exists d; intro Hm.
  rewrite (loop_sem m1), (loop_sem m2), <-(HI Hm); auto.
  
  (* maybe avoid abstracting length l1 *)
  intros; generalize (length (m1 L)); intro n; generalize m1 m2; 
   clear m1 m2; intros m1 m2.
  exists (WitD  n m1 m2). 
  generalize m1 m2; clear m1 m2; unfold WitD.
  induction n; intros m1 m2 Hm.
 
  (* base case *)
  unfold drestr.
  rewrite (eq_distr_intro _ 
   (Munit m1) (unroll_while_0_elim E (0%nat <! Elen L) c m1)),
   (eq_distr_intro _ (Munit m2) (unroll_while_0_elim E (0%nat <! Elen L) c m2)).
  rewrite 2 Mlet_unit. 
  simpl; unfold drestr; rewrite Mlet_unit; simpl.
  unfold negP, negb, EP; setoid_rewrite (@HI_syn _ _ _ Hm).
  eapply le_lift_weaken with ((I /-\ EP1 (Elen L =?= 0%nat)) k) R1 D0; auto.
  case_eq (E.eval_expr (0%nat <! Elen L) m1); intro Heq; setoid_rewrite Heq.
  eapply le_lift_eq_compat; [ apply Oeq_refl | | | | |
   apply le_lift_prod ]; auto.
  apply le_lift_Munit; auto.
  split; trivial; generalize Heq; clear Heq; expr_simpl;
   intro Heq; apply leb_complete_conv in Heq; apply nat_eqb_eq; omega.
  (* inductive case *)
  unfold drestr. 
  rewrite (Mlet_eq_compat (eq_distr_intro  _ _ (deno_cond_elim E (0%nat <! Elen L) 
   (c ++ unroll_while (0%nat <! Elen L) c n) nil m1)) (Oeq_refl _)),
  (Mlet_eq_compat (eq_distr_intro  _ _ (deno_cond_elim E (0%nat <! Elen L) 
   (c ++ unroll_while (0%nat <! Elen L) c n) nil m2)) (Oeq_refl _)).
  simpl WitIter; unfold DistrSel; simpl fst; simpl snd.
  setoid_rewrite (@HI_syn _ _ _ Hm).
  destr_sig.
  case_eq (@E.eval_expr _ T.Bool (0%nat <! Elen L) m1); intro Heq; 
   setoid_rewrite Heq.
  (* [guard = true] *)
  rewrite 2 deno_app, 2 Mcomp.
  destruct (list_eq_dec (@A_eqb_dec k) (firstn (Size k) (m1 L))
   (firstn (Size k) (m2 L))) as [Hhead | Hhead].
  (* same head *)
  destruct (req_mem_dec {{L}} m1 m2) as [ Heq' | Heq' ].
  (* same list *)
  apply le_lift_weaken with ((I /-\ EP1 (Elen L =?= 0%nat)) k)
   ((R1 * (lam k)))%R (max (D0 + R1 ** (ep k))%U ((ep k) + (lam k) ** D0)%U);
   [ trivial | auto with real | repeat multRU_simpl; repeat Usimpl; auto | ].
  eapply le_lift_Mlet with (R2:=(I /-\ kreq_mem {{L}}) k).
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd (conj Hm Heq'))).
  trivial.
  refine (Hd (conj Hm Heq')).
  intros m1' m2' Hm'.
  apply (IHn _ _ (proj1 Hm')).
  (* diff list *)
  apply le_lift_weaken with ((I /-\ EP1 (Elen L =?= 0%nat)) k)
   ((R1 * (lam k)))%R (max (D0 + R1 ** (ep k))%U ((ep k) + (lam k) ** D0)%U);
   [ trivial | auto with real | repeat multRU_simpl; repeat Usimpl; auto | ].
  destr_sig.
  assert (Hp: (I /-\ (fun (k : nat) (m1 m2 : Mem.t k) =>
   firstn (Size k) (m1 L) = firstn (Size k) (m2 L) /\ 
   m1 L <> m2 L)) _  m1 m2) by (repeat split; trivial; 
    intros H'; elim Heq'; intros t v Hv; 
     Vset_mem_inversion Hv; subst; trivial).
  eapply le_lift_Mlet.
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd0 Hp)).
  trivial.
  apply  (Hd0 Hp).
  intros m1' m2' Hm'.
  apply (IHn _ _ Hm').
  (* diff head *)
  apply le_lift_weaken with ((I /-\ EP1 (Elen L =?= 0%nat)) k)
   ((lam k) * R1)%R (max ((ep k) + (lam k) ** D0)%U (D0 + R1 ** (ep k))%U);
   [ trivial | auto with real | repeat multRU_simpl; repeat Usimpl; auto | ].
  destr_sig.
  eapply le_lift_Mlet.
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd0 (conj Hm Hhead))).
  trivial.
  apply (Hd0 (conj Hm Hhead)).
  intros m1' m2' Hm'. 
  refine (WitD_eq_L n (proj1 Hm') (proj2 Hm')). 
    (* [guard = false] *)
  rewrite 2 deno_nil, 3 Mlet_unit.
  eapply le_lift_weaken with  ((I /-\ EP1 (Elen L =?= 0%nat)) k) R1 D0; auto.
  eapply le_lift_eq_compat; [ apply Oeq_refl | | | | |
   apply (WitD_guard_false  n Hm Heq)  ]; auto.
 Qed.
  
End LOOP_RULE.  
