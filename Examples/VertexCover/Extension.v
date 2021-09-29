Require Export BuildTac.
Require Export Graph.

Set Implicit Arguments.

Unset Strict Implicit.

Parameter eps : R.

Parameter eps_pos : (0 < eps)%R.

Inductive Ut : Type := 
| Vertex
| Graph.
 
Inductive uop : Type :=
| Ot
| Ou
| Gin
| Gsize
| Gremove.

Inductive usupport_ (T_type:Type) (T_Nat:T_type) (T_User:Ut -> T_type) 
 (E_expr:T_type -> Type) : T_type -> Type :=
| weighted : forall (e:E_expr (T_User Graph)) (n i:E_expr T_Nat),
   usupport_ T_Nat T_User E_expr (T_User Vertex).


Module Sem (Gr:GRAPH) <: SEM.

 (* Auxiliary lemmas on Graphs *)
 Lemma Gr_v_eqb_refl : forall v, Gr.v_eqb v v = true.
 Proof.
  intro v; generalize (Gr.v_eqb_spec v v); case (Gr.v_eqb v v); tauto.
 Qed.

 Lemma Gr_v_eqb_true : forall v1 v2, Gr.v_eqb v1 v2 = true -> v1 = v2.
 Proof.
  intros v1 v2; generalize (Gr.v_eqb_spec v1 v2); case (Gr.v_eqb v1 v2).
  tauto.
  intros; discriminate.
 Qed.

 Lemma Gr_is_empty_dec : forall G, {Gr.is_empty G} + {~Gr.is_empty G}.
 Proof. 
  intro G'; destruct (Gr.is_empty G'); [left | right]; trivialb.
 Qed.


 Parameter t_ u_ : Gr.vertex.

 Hypothesis t_neq_u : t_ <> u_.
 
 (** * User-defined type module *)
 Module UT <: UTYPE.

  Definition t := Ut. 

  Definition eqb (x y:t) :=
   match x, y with
   | Vertex, Vertex => true
   | Graph, Graph => true
   | _,_ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros x y; case x; case y; simpl; trivial; discriminate.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True} :=
   match x as x0 return {x0 = y} + {True} with
   | Vertex => 
     match y as y0 return {Vertex = y0} + {True} with 
     | Vertex => left _ (refl_equal _) 
     | _ => right _ I
     end
   | Graph => 
     match y as y0 return {Graph = y0} + {True} with 
     | Graph => left _ (refl_equal _) 
     | _ => right _ I
     end  
  end.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   intros x y; case x; case y; simpl; intros; discriminate.
  Qed.

  Definition interp (k:nat) (t0:t) : Type := 
   match t0 with
   | Vertex => Gr.vertex
   | Graph => Gr.t
   end.

  Definition size k (t0:t) (_:interp k t0) := S O.

  Definition default k (t0:t) : interp k t0 := 
   match t0 with
   | Vertex => Gr.dummy_vertex
   | Graph => Gr.empty
   end.

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
   | Vertex => Gr.v_eqb
   | Graph => Gr.eqb
   end.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros; unfold i_eqb.
   destruct t0.
   apply Gr.v_eqb_spec.
   apply Gr.eqb_spec.
  Qed.

 End UT.

 Module T := MakeType UT.


 (** * Module for user-defined operators *)
 Module Uop <: UOP UT T.

  Definition t := uop.

  Definition eqb (o1 o2:t) : bool :=
   match o1, o2 with
    | Ot, Ot => true
    | Ou, Ou => true
    | Gin, Gin => true
    | Gsize, Gsize => true
    | Gremove, Gremove => true
    | _, _ => false
   end.

  Lemma eqb_spec :  forall x y, if eqb x y then x = y else x <> y.
  Proof.
   destruct x; destruct y; simpl; trivial; intro; discriminate.
  Qed.

  Definition targs (op : t) : list T.type :=
   match op with
    | Ot => nil
    | Ou => nil
    | Gin => T.User Graph :: T.User Vertex :: nil
    | Gsize => T.User Graph :: nil
    | Gremove => T.User Graph :: T.User Vertex :: nil
   end.

  Definition tres (op: t) : T.type :=
   match op with
    | Ot => T.User Vertex
    | Ou => T.User Vertex
    | Gin => T.Bool
    | Gsize => T.Nat
    | Gremove => T.User Graph
   end.

  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
    | Ot => u_
    | Ou => t_
    | Gin => Gr.in_graph
    | Gsize => Gr.size
    | Gremove => Gr.remove_vertex
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
    | Ot => (u_, O) 
    | Ou => (t_, O)
    | Gin => fun x y => (Gr.in_graph x y, Gr.size x)
    | Gsize => fun x => (Gr.size x, S O)
    | Gremove => fun x y => (Gr.remove_vertex x y, S O)
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

 Hint Resolve Rle_refl pos_INR exp_pos eps_pos.

 Module US <: USUPPORT UT T Var Mem Uop O E.

  Module VarP := MkEqBool_Leibniz_Theory Var.
  Module Vset := MkListSet VarP.Edec.

  Definition usupport := usupport_ T.Nat T.User E.expr.

  Definition w (i:nat) (n:nat) : R :=
   ((4 / eps) * sqrt (INR n / INR (n - i)))%R.

  Lemma w_pos : forall i n, (i < n)%nat -> 0 < w i n.
  Proof.
   intros; unfold w.
   apply Rmult_lt_0_compat.
   apply Rdiv_lt_0; [fourier | trivial].
   apply sqrt_lt_R0.
   apply Rdiv_lt_0; apply lt_0_INR; omega.  
  Qed.

 Definition weighted_choice (G:Gr.t) (i n:nat) : Distr Gr.vertex.
   intros G i n.
   destruct (le_lt_dec n i).
   exact (Munit Gr.dummy_vertex).

   destruct (Gr_is_empty_dec G).
   exact (Munit Gr.dummy_vertex).

   destruct (Gr.not_is_empty n0) as [a Ha].
   eapply finite_distr with 
    (l:=Gr.WS.elements (Gr.V G)) 
    (f:=fun v => (INR (Gr.degree G v) + w i n)) (a:=a).

   intros; apply Rplus_le_le_0_compat.
   apply pos_INR.
   apply Rlt_le, w_pos; trivial.
   apply Gr.in_graph_element with (1:=Ha).

   apply Rplus_le_lt_0_compat.
   apply pos_INR.
   apply w_pos; trivial.
  Defined.

  Definition carV (v:Gr.vertex) : MF Gr.vertex :=
   fun w => if Gr.v_eqb v w then 1%U else 0%tord.

  Lemma carV_prop : forall a, cover (@eq Gr.vertex a) (carV a).
  Proof.
   unfold carV; split; intros.
   subst; rewrite Gr_v_eqb_refl; trivial.
   generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro.
   exfalso; tauto.
   trivial.
  Qed.  

  Lemma weighted_choice_spec_in : forall G i n v, 
   (i < n)%nat ->
   Gr.in_graph G v ->
   Gr.size G = (n - i)%nat ->
   iR (mu (weighted_choice G i n) (carV v)%tord) =
   (INR (Gr.degree G v) + w i n) / (INR (Gr.weight G) + INR (n - i) * w i n).
  Proof.
   intros; unfold weighted_choice.
   destruct (le_lt_dec n i).
   exfalso; omega.

   destruct (Gr_is_empty_dec G0).
   exfalso.
   apply Gr.is_empty_size in i0; rewrite H1 in i0; omega.

   destruct (Gr.not_is_empty (g:=G0) n0).
   rewrite finite_distr_in.
   unfold c, y; rewrite retract_R.
   apply f_equal.

   rewrite fold_right_Rplus_plus.
   rewrite fold_right_Rplus_const.
   apply Rplus_eq_compat.

   rewrite <-map_map, fold_right_Rplus_INR, Gr.weight_def; trivial.

   fold Gr.WS.elt; rewrite (Gr.size_elements G0), H1; trivial.

   split.
   apply Rdiv_pos.
   apply Rplus_le_le_0_compat.
   apply pos_INR.
   apply Rlt_le, w_pos; trivial.

   eapply fold_right_Rplus_lt_0 with (y:=INR (Gr.degree G0 x) + w i n).
   apply in_map_iff; exists x; split.
   trivial.
   apply Gr.in_graph_element with (1:=i0).

   apply Rplus_le_lt_0_compat.
   auto.
   apply w_pos; trivial.

   apply map_pos; intros.
   apply Rplus_le_le_0_compat.
   apply pos_INR.
   apply Rlt_le, w_pos; trivial.

   apply Rdiv_le_1.
   eapply fold_right_Rplus_lt_0 with (y:=INR (Gr.degree G0 x) + w i n).
   apply in_map_iff; exists x; split.
   trivial.
   apply Gr.in_graph_element with (1:=i0).

   apply Rplus_le_lt_0_compat.
   auto.
   apply w_pos; trivial.

   apply map_pos; intros.
   subst; apply Rplus_le_le_0_compat.
   apply pos_INR.
   apply Rlt_le, w_pos; trivial.

   rewrite fold_right_Rplus_plus, fold_right_Rplus_const.

   apply Rplus_le_compat.

   rewrite <-map_map, fold_right_Rplus_INR.
   apply le_INR.
   apply Gr.in_graph_element in H0.
   clear -H0; induction (Gr.WS.elements); simpl; [elim H0 | ].
   simpl in H0; destruct H0.

   subst; omega.
   generalize (IHl H); intro; omega.

   fold Gr.WS.elt.
   rewrite (Gr.size_elements G0), H1.
   rewrite <-Rmult_1_l at 1; apply Rmult_le_compat.
   fourier.
   apply Rlt_le, w_pos; trivial.
   change 1 with (INR 1); apply le_INR; omega.
   trivial.

   apply carV_prop.

   apply Gr.NoDup_elements.

   apply Gr.in_graph_element with (1:=H0).
  Qed.

  Lemma weighted_choice_spec_notin : forall G i n v, 
   (i < n)% nat ->
   Gr.size G = (n - i)%nat ->
   ~Gr.in_graph G v ->
   mu (weighted_choice G i n) (carV v) == 0%tord.
  Proof.
   intros; unfold weighted_choice.
   destruct (le_lt_dec n i).
   exfalso; omega.

   destruct (Gr_is_empty_dec G0).
   exfalso.
   apply Gr.is_empty_size in i0; rewrite H0 in i0; omega.

   destruct (Gr.not_is_empty (g:=G0)).
   apply finite_distr_notin.
   apply carV_prop.

   intro; elim H1; apply Gr.in_graph_element; trivial.
  Qed.

  Lemma weighted_choice_in_graph : forall G i n, 
   (i < n)%nat ->
   Gr.size G = (n - i)%nat ->
   range (Gr.in_graph G) (US.weighted_choice G i n).
  Proof.
   intros G i n Hlt Hsize f Hf; unfold weighted_choice.
   destruct (le_lt_dec n i).
   exfalso; omega.

   destruct (Gr_is_empty_dec G); trivial.
   exfalso.
   apply Gr.is_empty_size in i0; rewrite Hsize in i0; omega.

   destruct (Gr.not_is_empty (g:=G) n0).
   simpl; symmetry; apply fold_right_Uplus_0; intros.
   rewrite <-Hf; [auto | ].
   apply Gr.in_graph_element; trivial.
  Qed.

  Definition eval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) :=
   match s with
    | weighted g i n =>
      weighted_choice (E.eval_expr g m) (E.eval_expr i m) (E.eval_expr n m)
   end.

  Definition ceval k t (s:usupport t) (m:Mem.t k) : Distr (T.interp k t) * nat :=
   match s with
    | weighted g i n =>
      (weighted_choice (E.eval_expr g m) (E.eval_expr i m) (E.eval_expr n m),
       Gr.size (E.eval_expr g m))
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
    | weighted g i n => Vset.union (fv_expr g) (Vset.union (fv_expr i) (fv_expr n))
   end.

  Module VsetP := MkSet_Theory Vset.
  
  Lemma depend_only_fv_distr : forall t (s:usupport t), 
   depend_only_distr (fv_distr s) s.
  Proof.
   intros t s k m1 m2 H; destruct s; simpl.
   simpl in H.
   rewrite depend_only_fv_expr with (e:=e) (m2:=m2).
   rewrite depend_only_fv_expr with (e:=i) (m2:=m2).
   rewrite depend_only_fv_expr with (e:=n) (m2:=m2).
   trivial.
   apply req_mem_weaken with (2:=H); auto with set.
   apply req_mem_weaken with (2:=H); auto with set.
   apply req_mem_weaken with (2:=H); auto with set.
  Qed.

  Lemma lossless_support : forall k t (s:usupport t) (m:Mem.t k),
   mu (eval s m) (fun _ => 1)%U == 1%U.
  Proof.
   intros; destruct s; simpl;unfold weighted_choice.  
   destruct (le_lt_dec (E.eval_expr i m) (E.eval_expr n m)); [trivial | ].
   destruct (Gr_is_empty_dec (E.eval_expr e m)); [trivial | ].
   destruct (Gr.not_is_empty (g:=E.eval_expr e m) n0).
   refine (finite_distr_lossless _ _ _ _ _ _).
  Qed.

  Lemma discrete_support : forall k t (s:usupport t) (m:Mem.t k),
   is_Discrete (eval s m).
  Proof.
   intros; destruct s; simpl.
   unfold weighted_choice.
   destruct (le_lt_dec (E.eval_expr i m) (E.eval_expr n m)).
   apply is_Discrete_Munit.

   destruct (Gr_is_empty_dec (E.eval_expr e m)).
   apply is_Discrete_Munit.

   destruct (Gr.not_is_empty (g:=E.eval_expr e m)).      
   apply finite_distr_discrete.
  Qed.

  Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
   match s1, s2 with
   | weighted g i n, weighted g' i' n' => E.eqb g g' && E.eqb i i' && E.eqb n n' 
   end.

  Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
   if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
   else ~eq_dep T.type usupport t1 e1 t2 e2.
  Proof.
   intros t1 [g1 i1 n1] t2 [g2 i2 n2]; simpl.
   generalize (E.eqb_spec g1 g2); destruct (E.eqb g1 g2);
   generalize (E.eqb_spec i1 i2); destruct (E.eqb i1 i2);
   generalize (E.eqb_spec n1 n2); destruct (E.eqb n1 n2);
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
 Notation "x |++| l" := 
  (E.Eop (O.Oappend _) {x,l}) (at level 60, right associativity).
 Notation Enth := (E.Eop (O.Onth _)).
 Notation "'Elen' p" := (E.Eop (O.Olength _) {p}) (at level 40).
 Notation "'Zlen' p" := (E.Eop (O.OZlength _) {p}) (at level 40).
 Notation "x 'is_in' y" := (E.Eop (O.Omem _) {x, y}) (at level 60).
 Notation "x 'not_in' y" := (! E.Eop (O.Omem _) {x, y}) (at level 60).

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

 (* support *)
 Notation "'{0,1}'" := DE.Dbool.
 Notation "'[0..' e ']'" := (DE.Dnat e)%nat.
 Notation "'[' e1 ',,' e2 ']'" := (DE.DZ e1 e2)%nat.

End Sem.


(** Semantics with optimizations *)
Module Entries (Gr:GRAPH). 

 Module SemO <: SEM_OPT.
 
  Module Sem := Sem Gr.
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


Declare Module Gr : GRAPH.

Module Ent := Entries Gr.

Module Tactics := BuildTac.Make Ent.
Export Tactics.


(* Some useful tactics *)
Ltac elim_assign := 
 rewrite (@deno_cons_elim _ _ (_ <- _)), Mlet_simpl, deno_assign_elim.
Ltac elim_random := 
 rewrite (@deno_cons_elim _ _ (_ <$- _)), Mlet_simpl, deno_random_elim.
Ltac elim_assert := 
 rewrite (@deno_cons_elim _ _ (Assert _)), Mlet_simpl, deno_assert_elim.

Ltac mem_upd_simpl :=
 repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff; 
  [ | discriminate])); trivial.
Ltac expr_simpl := 
 unfold EP1, EP2, notR, andR, orR, impR, E.eval_expr; simpl; 
  unfold O.eval_op; simpl; mem_upd_simpl.


(* Some Notation *)
Notation t := (E.Eop (O.Ouser Ot) (dnil _)).
Notation u := (E.Eop (O.Ouser Ou) (dnil _)).

Notation "v '\in' G" := (E.Eop (O.Ouser Gin) {G, v}) (at level 60).
Notation "G \ v" := (E.Eop (O.Ouser Gremove) {G, v}) (at level 60).
Notation "| G |" := (E.Eop (O.Ouser Gsize) {G}) (at level 60).

Notation "'choose'" :=
 (fun G i n => DE.Duser (@weighted T.type T.Nat T.User E.expr G i n))
 (at level 60).


Lemma sum_inv_sqrt : forall n,
  (sum_f_R0 (fun k : nat => / sqrt (INR (S k))) n <=  2 * sqrt (INR (S n)))%R.
Proof.
induction n.
   simpl; rewrite sqrt_1; fourier.
   rewrite tech5, IHn.
   apply Rmult_le_reg_l with (sqrt (INR (S (S n)))); 
     [ apply sqrt_lt_R0, lt_0_INR, lt_0_Sn |  ].
   rewrite Rmult_plus_distr_l.
   transitivity (2 * sqrt (INR (S (S n)) * INR (S n)) + 1)%R.
     apply Rplus_le_compat.
     rewrite Rmult_comm, Rmult_assoc, <-sqrt_mult, 
       (Rmult_comm (INR _)); auto. 
     apply Rfourier_eqLR_to_le; field.
     intro H; apply sqrt_eq_0 in H; rewrite S_INR in H;
       [ pose proof (pos_INR (S n)); fourier | auto ].
   rewrite <-(Rmult_comm (2 * _)%R), Rmult_assoc, sqrt_sqrt; [ | auto ].
   set (X:=sqrt (INR (S (S n)) * INR (S n))). 
   set (Y:=INR (S (S n))).
   cut (2 * X <= 2 * Y - 1)%R; [ intro; fourier | ].
   replace (2*Y-1)%R with (2 * (INR n) + 3)%R by
     (unfold Y; rewrite 2 S_INR, 2 Rmult_plus_distr_l; field).
   transitivity (2 * sqrt (Rsqr (INR n + 3/2)))%R.
     apply Rmult_le_compat_l; [ fourier | ].
     unfold X;  apply sqrt_le_1_alt.
     rewrite 2 S_INR; unfold Rsqr.
     match goal with
       |- (?A <= ?B)%R => 
         replace A with (INR n * INR n + 3 * INR n + 2)%R  by field; 
           replace B with (INR n * INR n + 3 * INR n + 9 / 4)%R by field
     end.
     fourier.
   rewrite sqrt_Rsqr; [ | pose proof (pos_INR n); fourier ].
   apply Rfourier_eqLR_to_le; field.
Qed.
